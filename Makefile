# Makefile — Lean 4 formalization via AXLE (axiommath.ai)
#
# All proofs live in lean/. AXLE handles Mathlib remotely; no local lake build needed.
# Lean binaries are managed by elan at ~/.elan/bin — make sure that is on your PATH.
# AXLE CLI is installed via: uv tool install axiom-axle
#
# Typical workflow:
#   1. make check          — verify all files type-check cleanly
#   2. make disprove       — stress-test claims (no counterexample = evidence of correctness)
#   3. make sorry2lemma    — inspect open subgoals (outputs extracted lemma stubs)
#   4. <fill in proofs>
#   5. make repair         — let AXLE attempt auto-repair on a file with broken proofs
#   6. make simplify       — clean up tactic proofs once all sorrys are closed
#   7. make extract        — split into per-theorem files for publication artifact

export PATH := $(HOME)/.elan/bin:$(PATH)

LEAN_DIR := HedonicGrouping
ENV      := lean-4.28.0
AXLE     := axle
TIMEOUT  := 120

DEFS    := $(LEAN_DIR)/Defs.lean
LEMMA1  := $(LEAN_DIR)/Lemma1.lean
LEMMA2  := $(LEAN_DIR)/Lemma2.lean

# Default target file for repair/sorry2lemma when FILE is not specified.
FILE ?= $(LEMMA2)

# Output directory for extract-theorems.
EXTRACT_DIR ?= $(LEAN_DIR)/extracted

.PHONY: all check check-defs check-lemma1 check-lemma2 \
        sorry2lemma disprove disprove-lemma1 disprove-lemma2 \
        simplify simplify-lemma1 simplify-lemma2 \
        extract repair help lean-version

# ── check ─────────────────────────────────────────────────────────────────────
# Type-check files against the AXLE-hosted Lean 4.28.0 + Mathlib environment.
# "okay: true" in output means the file is fully valid (sorrys still count as valid
# unless you add --strict, but they are flagged as warnings).
# Use check-strict for CI-style failure on any sorry.

all: check

check: check-defs check-lemma1 check-lemma2

check-defs:
	@echo "==> Checking $(DEFS)"
	$(AXLE) check --environment $(ENV) - < $(DEFS)

check-lemma1:
	@echo "==> Checking $(LEMMA1)"
	$(AXLE) check --environment $(ENV) - < $(LEMMA1)

check-lemma2:
	@echo "==> Checking $(LEMMA2)"
	$(AXLE) check --environment $(ENV) - < $(LEMMA2)

# Fail with non-zero exit code if there are any errors (sorrys included).
check-strict:
	@echo "==> Strict check: all files"
	$(AXLE) check --environment $(ENV) --strict - < $(DEFS)
	$(AXLE) check --environment $(ENV) --strict - < $(LEMMA1)
	$(AXLE) check --environment $(ENV) --strict - < $(LEMMA2)

# ── disprove ──────────────────────────────────────────────────────────────────
# Attempt to prove the *negation* of every theorem in a file.
# "failed to prove negation" = no counterexample found = positive evidence.
# "disproved_theorems: [...]" = a claim is wrong; revise it before proceeding.
# Timeout is per-file. Increase for complex goals: make disprove TIMEOUT=300

disprove: disprove-lemma1 disprove-lemma2

disprove-lemma1:
	@echo "==> Disprove: $(LEMMA1)"
	$(AXLE) disprove --environment $(ENV) --timeout-seconds $(TIMEOUT) - < $(LEMMA1)

disprove-lemma2:
	@echo "==> Disprove: $(LEMMA2)"
	$(AXLE) disprove --environment $(ENV) --timeout-seconds $(TIMEOUT) - < $(LEMMA2)

# ── sorry2lemma ───────────────────────────────────────────────────────────────
# Extract every `sorry` placeholder (and unsolved error goals) into standalone
# top-level lemmas, making the remaining proof obligations explicit.
# Outputs: JSON metadata + the modified Lean source with extracted stubs.
# Target a specific file: make sorry2lemma FILE=lean/Lemma2.lean
# Target specific theorems: make sorry2lemma FILE=lean/Lemma2.lean NAMES=foo,bar

NAMES ?=

sorry2lemma:
	@echo "==> Extracting sorrys from $(FILE)"
	$(AXLE) sorry2lemma --environment $(ENV) \
	    $(if $(NAMES),--names $(NAMES),) \
	    --reconstruct-callsite \
	    - < $(FILE)

# ── repair ────────────────────────────────────────────────────────────────────
# Attempt to automatically repair broken or incomplete proofs.
# Tries terminal tactics (default: grind) to close open goals.
# Outputs the repaired Lean source; redirect to file to apply:
#   make repair FILE=HedonicGrouping/Lemma2.lean > Lemma2_repaired.lean
# Target specific theorems: make repair NAMES=rotation_eliminates_less_preferred

repair:
	@echo "==> Attempting proof repair on $(FILE)"
	$(AXLE) repair-proofs --environment $(ENV) \
	    $(if $(NAMES),--names $(NAMES),) \
	    --terminal-tactics grind,simp,omega,decide \
	    - < $(FILE)

# ── simplify ──────────────────────────────────────────────────────────────────
# Clean up tactic proofs: remove redundant steps, shorten proof blocks.
# Run this after all sorrys are closed. Outputs the simplified Lean source.
# Redirect to apply: make simplify-lemma1 > Lemma1_simplified.lean

simplify: simplify-lemma1 simplify-lemma2

simplify-lemma1:
	@echo "==> Simplifying proofs in $(LEMMA1)"
	$(AXLE) simplify-theorems --environment $(ENV) - < $(LEMMA1)

simplify-lemma2:
	@echo "==> Simplifying proofs in $(LEMMA2)"
	$(AXLE) simplify-theorems --environment $(ENV) - < $(LEMMA2)

# ── extract ───────────────────────────────────────────────────────────────────
# Split each file into per-theorem .lean files with full dependency tracking.
# Output goes to EXTRACT_DIR (default: HedonicGrouping/extracted/).
# Use this to produce the publishable supplementary artifact.

extract:
	@echo "==> Extracting theorems from $(LEMMA1) → $(EXTRACT_DIR)"
	$(AXLE) extract-theorems --environment $(ENV) \
	    --output-dir $(EXTRACT_DIR) --force - < $(LEMMA1)
	@echo "==> Extracting theorems from $(LEMMA2) → $(EXTRACT_DIR)"
	$(AXLE) extract-theorems --environment $(ENV) \
	    --output-dir $(EXTRACT_DIR) --force - < $(LEMMA2)

# ── lean-version ──────────────────────────────────────────────────────────────
lean-version:
	@lean --version
	@lake --version
	@$(AXLE) --version
	@$(AXLE) environments

# ── help ──────────────────────────────────────────────────────────────────────
help:
	@echo "See README.md for full target documentation and AXLE workflow."
	@echo "AXLE environment: $(ENV)  |  Toolchain: $(HOME)/.elan/bin"
