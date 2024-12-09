class Ebmc < Formula
  desc "Model Checker for SystemVerilog"
  homepage "https://www.cprover.org/ebmc/"
  url "https://github.com/diffblue/hw-cbmc.git",
    tag: "ebmc-5.3",
    revision: "a7bf36c2fba8f7658932b5d83a0e1752668cd091"
  version "5.3"
  license "BSD-3-Clause"

  uses_from_macos "flex" => :build
  uses_from_macos "curl" => :build
  depends_on "bison" => :build

  def install
    system "make", "-C", "lib/cbmc/src", "minisat2-download"
    system "make", "-C", "src"
    system "mkdir", "-p", "#{prefix}/usr/bin"
    system "cp", "src/ebmc/ebmc", "#{prefix}/usr/bin/"
  end

  test do
    system "make", "-C", "regression/ebmc", "test"
  end
end
