#!/usr/bin/env python3

from __future__ import annotations

import argparse
import csv
import math
import platform
import socket
import statistics
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path


KNOWN_RESULTS = {"proved", "refuted"}
NONSOLVED_RESULTS = {"timeout", "error", "missing"}
ALL_RESULTS = KNOWN_RESULTS | NONSOLVED_RESULTS
BACKENDS = ("ictminisat", "minisat2", "cadical")
GEOMEAN_FLOOR = 0.005


@dataclass(frozen=True)
class ResultRow:
  benchmark: str
  backend: str
  seconds: float | None
  result: str


def parse_args() -> argparse.Namespace:
  parser = argparse.ArgumentParser(
    description="Analyze and report new IC3 SAT backend benchmark results.")
  parser.add_argument("--results", required=True, type=Path)
  parser.add_argument("--expected", required=True, type=Path)
  parser.add_argument("--report", required=True, type=Path)
  parser.add_argument("--suite-name", default="HWMCC 2017 single track")
  parser.add_argument("--timeout-seconds", required=True, type=int)
  parser.add_argument("--jobs", required=True, type=int)
  parser.add_argument("--compiler", default="clang++")
  parser.add_argument("--host-summary", default=None)
  parser.add_argument("--build-command", required=True)
  parser.add_argument("--benchmark-command", required=True)
  parser.add_argument("--raw-results-label", default=None)
  return parser.parse_args()


def read_expected(path: Path) -> dict[str, str]:
  with path.open(newline="", encoding="utf-8") as infile:
    reader = csv.DictReader(infile)
    if reader.fieldnames != ["benchmark", "expected"]:
      raise ValueError(f"{path} has unexpected header {reader.fieldnames!r}")
    expected = {}
    for row in reader:
      benchmark = row["benchmark"].strip()
      verdict = row["expected"].strip()
      if verdict not in {"proved", "refuted", "unknown"}:
        raise ValueError(f"unexpected expected verdict {verdict!r}")
      if benchmark in expected:
        raise ValueError(f"duplicate expected benchmark {benchmark}")
      expected[benchmark] = verdict
  return expected


def parse_seconds(raw: str, benchmark: str, backend: str) -> float | None:
  if raw == "":
    return None
  try:
    value = float(raw)
  except ValueError as exc:
    raise ValueError(
      f"invalid seconds value {raw!r} for {benchmark}/{backend}") from exc
  if value < 0:
    raise ValueError(f"negative seconds value for {benchmark}/{backend}")
  return value


def read_results(path: Path) -> list[ResultRow]:
  with path.open(newline="", encoding="utf-8") as infile:
    reader = csv.reader(infile)
    rows = []
    for index, row in enumerate(reader):
      if not row:
        continue
      if index == 0 and row == ["benchmark", "backend", "seconds", "result"]:
        continue
      if len(row) != 4:
        raise ValueError(f"{path} has malformed row {row!r}")
      benchmark = row[0].strip()
      backend = row[1].strip()
      seconds = parse_seconds(row[2].strip(), benchmark, backend)
      result = row[3].strip()
      rows.append(ResultRow(benchmark, backend, seconds, result))
  return rows


def geomean(values: list[float]) -> float | None:
  if not values:
    return None
  adjusted = [max(value, GEOMEAN_FLOOR) for value in values]
  return math.exp(sum(math.log(value) for value in adjusted) / len(adjusted))


def format_float(value: float | None) -> str:
  if value is None:
    return "-"
  return f"{value:.2f}"


def format_pct(num: int, den: int) -> str:
  if den == 0:
    return "-"
  return f"{100.0 * num / den:.1f}%"


def markdown_table(headers: list[str], rows: list[list[str]]) -> str:
  lines = [
    "| " + " | ".join(headers) + " |",
    "| " + " | ".join("---" for _ in headers) + " |",
  ]
  for row in rows:
    lines.append("| " + " | ".join(row) + " |")
  return "\n".join(lines)


def summarize(
  expected: dict[str, str], rows: list[ResultRow], timeout_seconds: int
) -> dict[str, object]:
  errors: list[str] = []
  by_pair: dict[tuple[str, str], ResultRow] = {}
  benchmarks_seen = set()
  backend_counts = Counter()
  blank_seconds_when_decisive = Counter()
  nonblank_seconds_when_nonsolved = Counter()

  for row in rows:
    benchmarks_seen.add(row.benchmark)
    backend_counts[row.backend] += 1
    if row.backend not in BACKENDS:
      errors.append(f"unexpected backend {row.backend!r}")
    if row.result not in ALL_RESULTS:
      errors.append(
        f"unexpected result {row.result!r} for {row.benchmark}/{row.backend}")
    key = (row.benchmark, row.backend)
    if key in by_pair:
      errors.append(f"duplicate row for {row.benchmark}/{row.backend}")
    by_pair[key] = row
    if row.result in KNOWN_RESULTS and row.seconds is None:
      blank_seconds_when_decisive[row.backend] += 1
    if row.result in NONSOLVED_RESULTS and row.seconds is not None:
      nonblank_seconds_when_nonsolved[row.backend] += 1
    if row.result in KNOWN_RESULTS and row.seconds is not None:
      if row.seconds > timeout_seconds + 0.01:
        errors.append(
          f"decisive runtime above timeout for {row.benchmark}/{row.backend}: "
          f"{row.seconds:.2f}s")
    if row.benchmark not in expected:
      errors.append(f"missing expected label for benchmark {row.benchmark}")

  expected_rows = len(expected) * len(BACKENDS)
  if len(rows) != expected_rows:
    errors.append(f"expected {expected_rows} rows, got {len(rows)}")

  for benchmark in expected:
    for backend in BACKENDS:
      if (benchmark, backend) not in by_pair:
        errors.append(f"missing row for {benchmark}/{backend}")

  total_known = sum(1 for verdict in expected.values() if verdict != "unknown")
  total_unknown = len(expected) - total_known

  outcome_counts: dict[str, Counter[str]] = {backend: Counter() for backend in BACKENDS}
  known_correct: dict[str, list[ResultRow]] = {backend: [] for backend in BACKENDS}
  wrong_decisive_rows: list[ResultRow] = []
  decisive_unknown_rows: dict[str, list[ResultRow]] = {backend: [] for backend in BACKENDS}

  summaries: dict[str, dict[str, object]] = {}

  for backend in BACKENDS:
    backend_rows = [row for row in rows if row.backend == backend]
    correct_times: list[float] = []
    par2_terms: list[float] = []
    par10_terms: list[float] = []
    correct_decisive = 0
    wrong_decisive = 0
    unsolved_known = 0
    decisive_on_unknown = 0
    timeout_unknown = 0
    error_unknown = 0

    for row in backend_rows:
      outcome_counts[backend][row.result] += 1
      verdict = expected.get(row.benchmark)
      if verdict is None:
        continue
      if verdict == "unknown":
        if row.result in KNOWN_RESULTS:
          decisive_on_unknown += 1
          decisive_unknown_rows[backend].append(row)
        elif row.result == "timeout":
          timeout_unknown += 1
        else:
          error_unknown += 1
        continue

      if row.result == verdict:
        correct_decisive += 1
        known_correct[backend].append(row)
        if row.seconds is not None:
          correct_times.append(row.seconds)
          par2_terms.append(row.seconds)
          par10_terms.append(row.seconds)
      elif row.result in KNOWN_RESULTS:
        wrong_decisive += 1
        wrong_decisive_rows.append(row)
        par2_terms.append(timeout_seconds * 2)
        par10_terms.append(timeout_seconds * 10)
      else:
        unsolved_known += 1
        par2_terms.append(timeout_seconds * 2)
        par10_terms.append(timeout_seconds * 10)

    summaries[backend] = {
      "correct_decisive": correct_decisive,
      "wrong_decisive": wrong_decisive,
      "unsolved_known": unsolved_known,
      "decisive_on_unknown": decisive_on_unknown,
      "timeout_unknown": timeout_unknown,
      "error_unknown": error_unknown,
      "median_seconds": statistics.median(correct_times) if correct_times else None,
      "mean_seconds": statistics.mean(correct_times) if correct_times else None,
      "geomean_seconds": geomean(correct_times),
      "par2": statistics.mean(par2_terms) if par2_terms else None,
      "par10": statistics.mean(par10_terms) if par10_terms else None,
      "blank_seconds_when_decisive": blank_seconds_when_decisive[backend],
      "nonblank_seconds_when_nonsolved": nonblank_seconds_when_nonsolved[backend],
    }

  unique_correct = Counter()
  unique_correct_rows: dict[str, list[ResultRow]] = defaultdict(list)
  for benchmark, verdict in expected.items():
    if verdict == "unknown":
      continue
    correct_rows = []
    for backend in BACKENDS:
      row = by_pair.get((benchmark, backend))
      if row is not None and row.result == verdict:
        correct_rows.append(row)
    if len(correct_rows) == 1:
      row = correct_rows[0]
      unique_correct[row.backend] += 1
      unique_correct_rows[row.backend].append(row)

  pairwise = []
  largest_regressions = []
  for left_index, left in enumerate(BACKENDS):
    for right in BACKENDS[left_index + 1:]:
      shared = []
      left_wins = 0
      right_wins = 0
      ties = 0
      ratios = []
      for benchmark, verdict in expected.items():
        if verdict == "unknown":
          continue
        left_row = by_pair.get((benchmark, left))
        right_row = by_pair.get((benchmark, right))
        if left_row is None or right_row is None:
          continue
        if left_row.result == verdict and right_row.result == verdict:
          if left_row.seconds is None or right_row.seconds is None:
            continue
          shared.append((benchmark, verdict, left_row.seconds, right_row.seconds))
          if left_row.seconds + 1e-9 < right_row.seconds:
            left_wins += 1
          elif right_row.seconds + 1e-9 < left_row.seconds:
            right_wins += 1
          else:
            ties += 1
          ratios.append(
            max(right_row.seconds, GEOMEAN_FLOOR) /
            max(left_row.seconds, GEOMEAN_FLOOR))

      pairwise.append({
        "left": left,
        "right": right,
        "shared_correct_solves": len(shared),
        "left_wins": left_wins,
        "right_wins": right_wins,
        "ties": ties,
        "left_speedup": geomean(ratios),
      })

      regressions = sorted(
        shared,
        key=lambda item: (
          max(item[3], GEOMEAN_FLOOR) / max(item[2], GEOMEAN_FLOOR)),
        reverse=True)
      for benchmark, verdict, left_seconds, right_seconds in regressions[:5]:
        largest_regressions.append({
          "benchmark": benchmark,
          "expected": verdict,
          "left": left,
          "right": right,
          "left_seconds": left_seconds,
          "right_seconds": right_seconds,
          "slowdown": max(right_seconds, GEOMEAN_FLOOR) /
          max(left_seconds, GEOMEAN_FLOOR),
        })

  largest_regressions.sort(key=lambda item: item["slowdown"], reverse=True)

  notable_rows = []
  seen_notables = set()

  for row in wrong_decisive_rows:
    key = ("wrong", row.benchmark, row.backend)
    if key not in seen_notables:
      notable_rows.append({
        "benchmark": row.benchmark,
        "expected": expected[row.benchmark],
        "note": f"wrong decisive result by {row.backend}",
      })
      seen_notables.add(key)

  for backend in BACKENDS:
    for row in sorted(unique_correct_rows[backend], key=lambda item: (
      float("inf") if item.seconds is None else item.seconds,
      item.benchmark))[:10]:
      key = ("unique", row.benchmark)
      if key not in seen_notables:
        notable_rows.append({
          "benchmark": row.benchmark,
          "expected": expected[row.benchmark],
          "note": f"unique correct solve by {backend}",
        })
        seen_notables.add(key)

  for regression in largest_regressions:
    key = ("regression", regression["benchmark"], regression["left"], regression["right"])
    if key not in seen_notables:
      notable_rows.append({
        "benchmark": regression["benchmark"],
        "expected": regression["expected"],
        "note":
          f"{regression['left']} faster than {regression['right']} by "
          f"{regression['slowdown']:.2f}x",
      })
      seen_notables.add(key)
    if len(notable_rows) >= 15:
      break

  combined_notable_rows = []
  combined_notable_map = {}
  for row in notable_rows:
    benchmark = row["benchmark"]
    existing = combined_notable_map.get(benchmark)
    if existing is None:
      combined = {
        "benchmark": benchmark,
        "expected": row["expected"],
        "note": row["note"],
      }
      combined_notable_map[benchmark] = combined
      combined_notable_rows.append(combined)
    else:
      existing["note"] += f"; {row['note']}"

  return {
    "errors": errors,
    "expected_count": len(expected),
    "total_known": total_known,
    "total_unknown": total_unknown,
    "summaries": summaries,
    "outcome_counts": outcome_counts,
    "pairwise": pairwise,
    "unique_correct": unique_correct,
    "notable_rows": combined_notable_rows,
    "by_pair": by_pair,
    "expected": expected,
    "backend_counts": backend_counts,
    "decisive_unknown_rows": decisive_unknown_rows,
    "wrong_decisive_rows": wrong_decisive_rows,
    "unique_correct_rows": unique_correct_rows,
  }


def build_notable_table(data: dict[str, object]) -> str:
  by_pair: dict[tuple[str, str], ResultRow] = data["by_pair"]  # type: ignore[assignment]
  expected: dict[str, str] = data["expected"]  # type: ignore[assignment]
  rows = []
  for entry in data["notable_rows"]:  # type: ignore[index]
    benchmark = entry["benchmark"]
    fastest_backend = "-"
    fastest_time = "-"
    backend_summaries = []
    decisive_rows = []
    for backend in BACKENDS:
      row = by_pair.get((benchmark, backend))
      if row is None:
        backend_summaries.append(f"{backend}: missing@-s")
        continue
      seconds = format_float(row.seconds)
      backend_summaries.append(f"{backend}: {row.result}@{seconds}s")
      if row.result in KNOWN_RESULTS and row.seconds is not None:
        decisive_rows.append((row.seconds, backend))
    if decisive_rows:
      decisive_rows.sort()
      fastest_time_value, fastest_backend = decisive_rows[0]
      fastest_time = format_float(fastest_time_value)
    rows.append([
      benchmark,
      expected[benchmark],
      fastest_backend,
      fastest_time,
      "; ".join(backend_summaries),
      entry["note"],
    ])
  return markdown_table(
    [
      "benchmark",
      "expected",
      "fastest backend",
      "fastest time (s)",
      "results",
      "note",
    ],
    rows or [["-", "-", "-", "-", "-", "-"]])


def render_report(
  args: argparse.Namespace, expected: dict[str, str], data: dict[str, object]
) -> str:
  summaries = data["summaries"]
  outcome_counts = data["outcome_counts"]
  unique_correct = data["unique_correct"]
  pairwise = data["pairwise"]
  errors = data["errors"]
  unique_correct_rows = data["unique_correct_rows"]

  corpus_table = markdown_table(
    ["total", "expected proved", "expected refuted", "expected unknown"],
    [[
      str(len(expected)),
      str(sum(1 for verdict in expected.values() if verdict == "proved")),
      str(sum(1 for verdict in expected.values() if verdict == "refuted")),
      str(sum(1 for verdict in expected.values() if verdict == "unknown")),
    ]])

  overall_rows = []
  accuracy_rows = []
  unknown_rows = []
  runtime_rows = []
  unique_rows = []

  for backend in BACKENDS:
    summary = summaries[backend]
    counts = outcome_counts[backend]
    overall_rows.append([
      backend,
      str(counts["proved"]),
      str(counts["refuted"]),
      str(counts["timeout"]),
      str(counts["error"]),
      str(counts["missing"]),
    ])
    accuracy_rows.append([
      backend,
      str(summary["correct_decisive"]),
      str(summary["wrong_decisive"]),
      str(summary["unsolved_known"]),
      format_pct(summary["correct_decisive"], data["total_known"]),
    ])
    unknown_rows.append([
      backend,
      str(summary["decisive_on_unknown"]),
      str(summary["timeout_unknown"]),
      str(summary["error_unknown"]),
    ])
    runtime_rows.append([
      backend,
      format_float(summary["median_seconds"]),
      format_float(summary["geomean_seconds"]),
      format_float(summary["mean_seconds"]),
      format_float(summary["par2"]),
      format_float(summary["par10"]),
    ])
    unique_rows.append([backend, str(unique_correct[backend])])

  pairwise_rows = []
  for item in pairwise:
    pairwise_rows.append([
      f"{item['left']} vs {item['right']}",
      str(item["shared_correct_solves"]),
      str(item["left_wins"]),
      str(item["right_wins"]),
      str(item["ties"]),
      format_float(item["left_speedup"]),
    ])

  raw_results_label = args.raw_results_label or str(args.results)
  host = args.host_summary or f"{socket.gethostname()} ({platform.platform()})"

  best_correct_backend = max(
    BACKENDS, key=lambda backend: summaries[backend]["correct_decisive"])
  best_par2_backend = min(
    BACKENDS, key=lambda backend: summaries[backend]["par2"])
  wrong_decisive_total = sum(
    int(summaries[backend]["wrong_decisive"]) for backend in BACKENDS)
  best_vs_default = next(
    item for item in pairwise
    if item["left"] == "ictminisat" and item["right"] == "minisat2")
  cadical_unique = ", ".join(
    row.benchmark for row in unique_correct_rows["cadical"]) or "none"
  minisat2_margin = (
    int(summaries["minisat2"]["correct_decisive"]) -
    int(summaries["ictminisat"]["correct_decisive"]))
  cadical_margin = (
    int(summaries["cadical"]["correct_decisive"]) -
    int(summaries["ictminisat"]["correct_decisive"]))

  lines = [
    "# New IC3 SAT Backend Benchmark on HWMCC 2017",
    "",
    "This report compares the `ictminisat`, `minisat2`, and `cadical` SAT",
    "backends for `ebmc --new-ic3` on the full HWMCC 2017 single-track suite.",
    "",
    "## Setup",
    "",
    f"- Suite: `{args.suite_name}`",
    f"- Compiler: `{args.compiler}`",
    f"- Build cache: `ccache`",
    f"- Timeout: `{args.timeout_seconds}` seconds per benchmark/backend",
    f"- Parallel jobs: `{args.jobs}`",
    f"- Host: `{host}`",
    f"- Build command: `{args.build_command}`",
    f"- Benchmark command: `{args.benchmark_command}`",
    f"- Expected labels: `{args.expected}`",
    f"- Raw results: `{raw_results_label}`",
    "",
    "## Key Findings",
    "",
    f"- `minisat2` had the best known-label coverage at "
    f"`{summaries['minisat2']['correct_decisive']}/{data['total_known']}` "
    f"correct solves, `{minisat2_margin:+d}` versus `ictminisat` and "
    f"`{int(summaries['minisat2']['correct_decisive']) - int(summaries['cadical']['correct_decisive']):+d}` versus `cadical`.",
    f"- `minisat2` also had the best PAR-2 score at "
    f"`{format_float(summaries['minisat2']['par2'])}` seconds; on the "
    f"`{best_vs_default['shared_correct_solves']}` cases solved correctly by "
    f"both MiniSAT-based backends, `ictminisat` vs `minisat2` yielded a "
    f"`{format_float(best_vs_default['left_speedup'])}x` geomean speedup for "
    f"`ictminisat`, so `minisat2` wins overall by solving two additional "
    f"known-label cases rather than by being faster on the shared subset.",
    f"- `cadical` solved fewer known-label cases "
    f"(`{summaries['cadical']['correct_decisive']}/{data['total_known']}`, "
    f"`{cadical_margin:+d}` versus `ictminisat`) but did contribute "
    f"`{data['unique_correct']['cadical']}` unique correct solve(s): "
    f"`{cadical_unique}`.",
    f"- Wrong decisive results observed: `{wrong_decisive_total}`.",
    "",
    "## Recommendation",
    "",
    f"- Keep SAT-backend selection user-visible via "
    f"`--new-ic3-sat-solver`.",
    f"- If we want to change the default based on HWMCC 2017 alone, "
    f"`{best_correct_backend}` is the strongest candidate on solved-count "
    f"grounds and `{best_par2_backend}` is best on PAR-2.",
    "- Keep `cadical` as an opt-in backend rather than the default; it offers "
    "niche coverage gains but loses materially on aggregate throughput.",
    "",
    "## Corpus Summary",
    "",
    corpus_table,
    "",
    "## Overall Outcome Counts",
    "",
    markdown_table(
      ["backend", "proved", "refuted", "timeout", "error", "missing"],
      overall_rows),
    "",
    "## Known-Label Accuracy",
    "",
    markdown_table(
      [
        "backend",
        "correct decisive",
        "wrong decisive",
        "unsolved known",
        "known solved rate",
      ],
      accuracy_rows),
    "",
    "## Unknown-Label Behavior",
    "",
    markdown_table(
      ["backend", "decisive on unknown", "timeout unknown", "error unknown"],
      unknown_rows),
    "",
    "## Runtime Summary",
    "",
    "Correct decisive runtimes use the CSV's centisecond timing. PAR scores are",
    f"computed on the {data['total_known']} known-label benchmarks with penalties",
    f"of `{args.timeout_seconds * 2}` seconds for PAR-2 and",
    f"`{args.timeout_seconds * 10}` seconds for PAR-10.",
    "",
    markdown_table(
      ["backend", "median s", "geomean s", "mean s", "PAR-2", "PAR-10"],
      runtime_rows),
    "",
    "## Unique Correct Solves",
    "",
    markdown_table(["backend", "unique correct solves"], unique_rows),
    "",
    "## Pairwise Shared Correct Solves",
    "",
    "Geomean speedup is reported for the left backend over the right backend;",
    "values above `1.00` favor the left backend.",
    "",
    markdown_table(
      ["pair", "shared correct", "left wins", "right wins", "ties", "geomean speedup"],
      pairwise_rows),
    "",
    "## Notable Benchmarks",
    "",
    build_notable_table(data),
    "",
    "## Sanity Checks",
    "",
    markdown_table(
      ["backend", "blank decisive seconds", "nonblank nonsolved seconds"],
      [[
        backend,
        str(summaries[backend]["blank_seconds_when_decisive"]),
        str(summaries[backend]["nonblank_seconds_when_nonsolved"]),
      ] for backend in BACKENDS]),
    "",
  ]

  if errors:
    lines.extend([
      "## Reported Issues",
      "",
      "The following sanity checks failed and should be addressed before relying",
      "on the benchmark summary:",
      "",
    ])
    for error in errors:
      lines.append(f"- {error}")
    lines.append("")

  wrong_decisive_rows = data["wrong_decisive_rows"]
  if wrong_decisive_rows:
    lines.extend([
      "## Wrong Decisive Results",
      "",
      markdown_table(
        ["benchmark", "backend", "expected", "observed", "seconds"],
        [[
          row.benchmark,
          row.backend,
          expected[row.benchmark],
          row.result,
          format_float(row.seconds),
        ] for row in sorted(
          wrong_decisive_rows, key=lambda row: (row.benchmark, row.backend))]),
      "",
    ])

  return "\n".join(lines)


def main() -> int:
  args = parse_args()

  try:
    expected = read_expected(args.expected)
    rows = read_results(args.results)
    data = summarize(expected, rows, args.timeout_seconds)
    report = render_report(args, expected, data)
  except Exception as exc:  # pylint: disable=broad-except
    print(f"error: {exc}", file=sys.stderr)
    return 1

  args.report.write_text(report, encoding="utf-8")
  if data["errors"]:
    print(f"warning: wrote report with {len(data['errors'])} sanity issues")
    return 2

  print(args.report)
  return 0


if __name__ == "__main__":
  sys.exit(main())
