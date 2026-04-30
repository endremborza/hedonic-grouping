# Makefile — Lean 4 formalization via AXLE (axiommath.ai)
#
# AXLE only supports `import Mathlib`, so per-file checks concatenate the
# target with all of its HedonicGrouping dependencies via
# `scripts/concat_imports.py`. No hand-maintained cat chains.
#
# Workflow:
#   make check          — type-check every leaf file
#   make check-FILE=... — check one file and its deps
#   make disprove       — stress-test claims (no counterexample = evidence)
#   make sorry2lemma    — inspect open subgoals
#   make repair         — auto-repair attempts
#   make simplify       — clean up tactic proofs after all sorrys are closed

export PATH := $(HOME)/.elan/bin:$(PATH)

LEAN_DIR := HedonicGrouping
ENV      := lean-4.28.0
AXLE     := axle
TIMEOUT  := 120
CONCAT   := python3 scripts/concat_imports.py

# All leaf files to check. Add new files here as they appear.
LEAF_FILES := \
    $(LEAN_DIR)/Core.lean \
    $(LEAN_DIR)/Problems/SMP.lean \
    $(LEAN_DIR)/Problems/RMP.lean \
    $(LEAN_DIR)/Problems/HCP.lean \
    $(LEAN_DIR)/Algorithms/GaleShapley.lean \
    $(LEAN_DIR)/Algorithms/Irving.lean \
    $(LEAN_DIR)/Unification.lean \
    $(LEAN_DIR)/Correctness/GS_SMP.lean \
    $(LEAN_DIR)/Correctness/IRV_RMP.lean \
    $(LEAN_DIR)/Summary.lean

# Default target file for repair/sorry2lemma when FILE is not specified.
FILE ?= $(LEAN_DIR)/Algorithms/Irving.lean

# Output directory for extract-theorems.
EXTRACT_DIR ?= $(LEAN_DIR)/extracted

.PHONY: all check check-one disprove disprove-one \
        sorry2lemma repair simplify simplify-one \
        extract help lean-version python-check

# ── check ─────────────────────────────────────────────────────────────────────

all: check

python-check:
	python -m src.test_algorithms

check:
	@set -e; for f in $(LEAF_FILES); do \
	    echo "==> Checking $$f"; \
	    $(CONCAT) $$f | $(AXLE) check --environment $(ENV) -; \
	done

# Check one file: make check-one FILE=HedonicGrouping/Unification.lean
check-one:
	@echo "==> Checking $(FILE)"
	@$(CONCAT) $(FILE) | $(AXLE) check --environment $(ENV) -

# Strict check: fail on any sorry.
check-strict:
	@set -e; for f in $(LEAF_FILES); do \
	    echo "==> Strict check: $$f"; \
	    $(CONCAT) $$f | $(AXLE) check --environment $(ENV) --strict -; \
	done

# ── disprove ──────────────────────────────────────────────────────────────────

disprove:
	@set -e; for f in $(LEAF_FILES); do \
	    echo "==> Disprove: $$f"; \
	    $(CONCAT) $$f | $(AXLE) disprove --environment $(ENV) --timeout-seconds $(TIMEOUT) -; \
	done

disprove-one:
	@echo "==> Disprove: $(FILE)"
	@$(CONCAT) $(FILE) | $(AXLE) disprove --environment $(ENV) --timeout-seconds $(TIMEOUT) -

# ── sorry2lemma ───────────────────────────────────────────────────────────────

NAMES ?=

sorry2lemma:
	@echo "==> Extracting sorrys from $(FILE)"
	@$(CONCAT) $(FILE) | $(AXLE) sorry2lemma --environment $(ENV) \
	    $(if $(NAMES),--names $(NAMES),) \
	    --reconstruct-callsite \
	    -

# ── repair ────────────────────────────────────────────────────────────────────

repair:
	@echo "==> Attempting proof repair on $(FILE)"
	@$(CONCAT) $(FILE) | $(AXLE) repair-proofs --environment $(ENV) \
	    $(if $(NAMES),--names $(NAMES),) \
	    --terminal-tactics grind,simp,omega,decide \
	    -

# ── simplify ──────────────────────────────────────────────────────────────────

simplify:
	@set -e; for f in $(LEAF_FILES); do \
	    echo "==> Simplifying $$f"; \
	    $(CONCAT) $$f | $(AXLE) simplify-theorems --environment $(ENV) -; \
	done

simplify-one:
	@echo "==> Simplifying $(FILE)"
	@$(CONCAT) $(FILE) | $(AXLE) simplify-theorems --environment $(ENV) -

# ── extract ───────────────────────────────────────────────────────────────────

extract:
	@for f in $(LEAF_FILES); do \
	    echo "==> Extracting from $$f → $(EXTRACT_DIR)"; \
	    $(CONCAT) $$f | $(AXLE) extract-theorems --environment $(ENV) \
	        --output-dir $(EXTRACT_DIR) --force -; \
	done

# ── lean-version ──────────────────────────────────────────────────────────────

lean-version:
	@lean --version
	@lake --version
	@$(AXLE) --version
	@$(AXLE) environments

help:
	@echo "Targets:"
	@echo "  check           — type-check every leaf file"
	@echo "  check-one       — check one file (FILE=...)"
	@echo "  disprove        — stress-test claims"
	@echo "  sorry2lemma     — extract sorry goals (FILE=..., NAMES=...)"
	@echo "  repair          — auto-repair attempts (FILE=..., NAMES=...)"
	@echo "  simplify        — clean up tactic proofs"
	@echo "  python-check    — run Python reference tests"
