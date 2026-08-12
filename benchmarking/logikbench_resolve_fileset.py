#!/usr/bin/env python3

"""Resolve file sets from LogikBench benchmark definitions.

LogikBench benchmarks define their source files, include directories, and
preprocessor defines using the SiliconCompiler Design API.  This script
loads a benchmark module without requiring a full SiliconCompiler
installation by providing lightweight stubs, then extracts and writes out
the resolved file lists.

Usage:
    logikbench_resolve_fileset.py <benchmark.py> \
        --logikbench-root <path> \
        --lambdalib-root <path> \
        --sources-out <sources.txt> \
        --incdirs-out <incdirs.txt> \
        --defines-out <defines.txt> \
        [--fileset rtl]
"""

import argparse
import importlib.util
import sys
import types
from collections import defaultdict
from contextlib import contextmanager
from pathlib import Path


# ---------------------------------------------------------------------------
# Stub classes that stand in for the real SiliconCompiler / Jinja2 modules.
# ---------------------------------------------------------------------------


class _DummyTemplate:
    """No-op replacement for jinja2.Template."""

    def __init__(self, _text):
        pass

    def render(self, **_kwargs):
        # Benchmarks may call Template.render(); return empty string
        # since we only care about file lists, not generated content.
        return ""


class Design:
    """Lightweight stand-in for siliconcompiler.Design.

    Records files, include directories, defines, and dependency relationships
    that benchmarks declare via the SiliconCompiler API, without performing
    any actual compilation or synthesis.
    """

    def __init__(self, name=None):
        self.name = name
        self._dataroots = {}           # name -> resolved Path
        self._files = defaultdict(list)   # fileset -> [Path, ...]
        self._idirs = defaultdict(list)   # fileset -> [Path, ...]
        self._defines = defaultdict(list) # fileset -> [str, ...]
        self._deps = defaultdict(list)    # fileset -> [(Design, fileset), ...]
        self._fileset_stack = []       # stack for active_fileset context
        self._dataroot_stack = []      # stack for active_dataroot context

    def set_name(self, name):
        self.name = name

    def set_dataroot(self, name, path):
        """Register a named data root directory.

        If *path* points to a file, its parent directory is used instead.
        """
        dataroot = Path(path)
        # Some benchmarks pass __file__ as the data root; use its
        # containing directory so relative paths resolve correctly.
        if dataroot.is_file():
            dataroot = dataroot.parent
        self._dataroots[name] = dataroot.resolve()

    @contextmanager
    def active_dataroot(self, name):
        """Context manager that sets the implicit data root for file paths."""
        self._dataroot_stack.append(name)
        try:
            yield
        finally:
            # Restore previous data root when leaving the with-block.
            self._dataroot_stack.pop()

    @contextmanager
    def active_fileset(self, fileset):
        """Context manager that sets the implicit target fileset."""
        self._fileset_stack.append(fileset)
        try:
            yield
        finally:
            # Restore previous fileset when leaving the with-block.
            self._fileset_stack.pop()

    # Unsupported SiliconCompiler API calls — accept and ignore.
    # These are called by benchmark scripts but have no effect on
    # file-set resolution.
    def set_topmodule(self, *_args, **_kwargs):
        pass

    def set_param(self, *_args, **_kwargs):
        pass

    def _current_fileset(self, fileset):
        """Return the explicit fileset, or fall back to the stack."""
        if fileset is not None:
            return fileset
        if not self._fileset_stack:
            # No explicit fileset given and none on the stack — programmer error.
            raise ValueError("no active fileset")
        return self._fileset_stack[-1]

    def _current_dataroot(self, dataroot):
        """Return the explicit data root name, or fall back to the stack."""
        if dataroot is not None:
            return dataroot
        if self._dataroot_stack:
            return self._dataroot_stack[-1]
        # None means paths will be kept as-is (relative or absolute).
        return None

    def _resolve_path(self, item, dataroot=None):
        """Resolve *item* relative to the named data root, if any."""
        root_name = self._current_dataroot(dataroot)
        path = Path(item)
        # Absolute paths need no resolution.
        if path.is_absolute():
            return path
        # Without a data root, keep the path relative.
        if root_name is None:
            return path
        # Prepend the data root directory to get an absolute path.
        return self._dataroots[root_name] / path

    def add_file(self, item, fileset=None, dataroot=None):
        """Add one or more source files to a fileset."""
        fileset_name = self._current_fileset(fileset)
        # The SiliconCompiler API accepts both single paths and lists.
        if isinstance(item, (list, tuple)):
            for entry in item:
                self.add_file(entry, fileset=fileset_name, dataroot=dataroot)
            return
        self._files[fileset_name].append(self._resolve_path(item, dataroot))

    def add_idir(self, item, fileset=None, dataroot=None):
        """Add one or more include directories to a fileset."""
        fileset_name = self._current_fileset(fileset)
        # Same list-handling logic as add_file.
        if isinstance(item, (list, tuple)):
            for entry in item:
                self.add_idir(entry, fileset=fileset_name, dataroot=dataroot)
            return
        self._idirs[fileset_name].append(self._resolve_path(item, dataroot))

    def add_define(self, value, fileset=None):
        """Add a preprocessor define to a fileset."""
        fileset_name = self._current_fileset(fileset)
        self._defines[fileset_name].append(value)

    def add_depfileset(self, design, depfileset=None, fileset=None):
        """Declare a dependency on another design's fileset.

        When this fileset is collected, the dependent design's fileset
        will be collected transitively as well.
        """
        fileset_name = self._current_fileset(fileset)
        # Default: depend on the same-named fileset in the other design.
        depfileset_name = depfileset or fileset_name
        self._deps[fileset_name].append((design, depfileset_name))

    def write_fileset(self, path, fileset="rtl"):
        """Write resolved source file paths to *path*, one per line."""
        files, _, _ = collect_fileset(self, fileset)
        with open(path, "w", encoding="utf-8") as out:
            for filename in files:
                out.write(f"{filename}\n")


# ---------------------------------------------------------------------------
# Fileset collection helpers.
# ---------------------------------------------------------------------------


def ordered_unique(items):
    """Deduplicate *items* while preserving insertion order."""
    seen = set()
    result = []
    for item in items:
        if item in seen:
            continue
        seen.add(item)
        result.append(item)
    return result


def collect_fileset(design, fileset, seen=None):
    """Recursively collect files, include dirs, and defines for a fileset.

    Follows dependency edges (add_depfileset) transitively, avoiding cycles
    via the *seen* set of (design-id, fileset) pairs.

    Returns:
        Tuple of (files, idirs, defines), each a deduplicated list.
    """
    if seen is None:
        seen = set()

    # Use object id + fileset name as a cycle-detection key, since the
    # same Design object may appear in multiple dependency chains.
    key = (id(design), fileset)
    if key in seen:
        # Already visited — prevent infinite recursion on circular deps.
        return [], [], []

    seen.add(key)

    # Start with this design's own files/idirs/defines for this fileset.
    files = list(design._files.get(fileset, []))
    idirs = list(design._idirs.get(fileset, []))
    defines = list(design._defines.get(fileset, []))

    # Recursively pull in everything from dependent designs.
    for dep_design, depfileset in design._deps.get(fileset, []):
        dep_files, dep_idirs, dep_defines = collect_fileset(
            dep_design, depfileset, seen
        )
        files.extend(dep_files)
        idirs.extend(dep_idirs)
        defines.extend(dep_defines)

    # Deduplicate while keeping the first occurrence of each entry.
    return (
        ordered_unique(files),
        ordered_unique(idirs),
        ordered_unique(defines),
    )


# ---------------------------------------------------------------------------
# Module-loading infrastructure.
# ---------------------------------------------------------------------------


def install_stubs():
    """Install fake siliconcompiler and jinja2 modules into sys.modules.

    This allows benchmark scripts to ``import siliconcompiler`` and use
    its Design class without a real SiliconCompiler installation.
    """
    # Create a fake 'siliconcompiler' package exposing our Design stub.
    siliconcompiler = types.ModuleType("siliconcompiler")
    siliconcompiler.Design = Design
    # ASIC is a Design variant some benchmarks import; an empty subclass suffices.
    siliconcompiler.ASIC = type("ASIC", (Design,), {})
    sys.modules["siliconcompiler"] = siliconcompiler

    # Some benchmarks import siliconcompiler.library for LibrarySchema.
    siliconcompiler_library = types.ModuleType("siliconcompiler.library")
    siliconcompiler_library.LibrarySchema = type("LibrarySchema", (), {})
    sys.modules["siliconcompiler.library"] = siliconcompiler_library

    # Stub out jinja2 since some benchmark files use Template for docs.
    jinja2 = types.ModuleType("jinja2")
    jinja2.Template = _DummyTemplate
    sys.modules["jinja2"] = jinja2


def load_design_class(module_path):
    """Dynamically load a benchmark module and return its Design subclass.

    Raises RuntimeError if the module does not define exactly one Design
    subclass.
    """
    # Load the benchmark script as a module with a synthetic name so it
    # can use normal import statements internally.
    spec = importlib.util.spec_from_file_location(
        "__logikbench_target__", module_path
    )
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    # Execute the module — this triggers its class definitions and any
    # top-level code (which populates the Design via __init__).
    spec.loader.exec_module(module)

    # Find the single Design subclass defined directly in this module.
    # We filter by __module__ to exclude base classes or imports.
    design_classes = [
        obj
        for obj in module.__dict__.values()
        if isinstance(obj, type)
        and issubclass(obj, Design)
        and obj is not Design
        and obj.__module__ == module.__name__
    ]

    if len(design_classes) != 1:
        raise RuntimeError(
            f"expected exactly one design class in {module_path}, got "
            f"{len(design_classes)}"
        )

    return design_classes[0]


# ---------------------------------------------------------------------------
# Output helpers and entry point.
# ---------------------------------------------------------------------------


def write_lines(path, values):
    """Write each element of *values* as a line in a text file."""
    with open(path, "w", encoding="utf-8") as out:
        for value in values:
            out.write(f"{value}\n")


def main():
    parser = argparse.ArgumentParser(
        description="Resolve a LogikBench fileset into source/incdir/define lists."
    )
    parser.add_argument("benchmark", help="Path to the benchmark .py file")
    parser.add_argument("--logikbench-root", required=True,
                        help="Root of the LogikBench repository")
    parser.add_argument("--lambdalib-root", required=True,
                        help="Root of the lambdalib repository")
    parser.add_argument("--sources-out", required=True,
                        help="Output file for resolved source paths")
    parser.add_argument("--incdirs-out", required=True,
                        help="Output file for include directories")
    parser.add_argument("--defines-out", required=True,
                        help="Output file for preprocessor defines")
    parser.add_argument("--fileset", default="rtl",
                        help="Fileset to resolve (default: rtl)")
    args = parser.parse_args()

    # Inject stub modules before any benchmark code runs, so that
    # 'import siliconcompiler' resolves to our lightweight Design class.
    install_stubs()

    # Make LogikBench and lambdalib importable by the benchmark script,
    # since benchmarks typically do 'from logikbench... import ...' or
    # 'from lambdalib... import ...'.
    sys.path.insert(0, str(Path(args.logikbench_root).resolve()))
    sys.path.insert(0, str(Path(args.lambdalib_root).resolve()))

    # Load and instantiate the benchmark's Design subclass.  The __init__
    # method typically calls add_file/add_idir/add_define to register all
    # the design's source files.
    design_class = load_design_class(Path(args.benchmark).resolve())
    design = design_class()

    # Collect everything transitively from the requested fileset.
    files, idirs, defines = collect_fileset(design, args.fileset)

    # Include the parent directory of each source file as an implicit
    # include directory, matching typical Verilog tool behavior where
    # `include directives resolve relative to the including file.
    source_dirs = [filename.parent for filename in files]
    idirs = ordered_unique(idirs + source_dirs)

    # Write out the three resolved lists, one entry per line.
    write_lines(args.sources_out, files)
    write_lines(args.incdirs_out, idirs)
    write_lines(args.defines_out, defines)


if __name__ == "__main__":
    main()
