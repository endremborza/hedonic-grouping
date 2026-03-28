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

DEFS         := $(LEAN_DIR)/Defs.lean
GALESHAPLEY  := $(LEAN_DIR)/GaleShapley.lean
IRVING       := $(LEAN_DIR)/Irving.lean

# AXLE only supports `import Mathlib` — files that import Defs must be
# concatenated with Defs.lean (stripping their local imports) before sending.
define cat_with_defs
	(cat $(DEFS); echo; grep -v '^import ' $(1))
endef

# Default target file for repair/sorry2lemma when FILE is not specified.
FILE ?= $(IRVING)

# Output directory for extract-theorems.
EXTRACT_DIR ?= $(LEAN_DIR)/extracted

.PHONY: all check check-defs check-gs check-irving \
        sorry2lemma disprove disprove-gs disprove-irving \
        simplify simplify-gs simplify-irving \
        extract repair help lean-version

# ── check ─────────────────────────────────────────────────────────────────────
# Type-check files against the AXLE-hosted Lean 4.28.0 + Mathlib environment.
# "okay: true" in output means the file is fully valid (sorrys still count as valid
# unless you add --strict, but they are flagged as warnings).
# Use check-strict for CI-style failure on any sorry.

all: check

check: check-defs check-gs check-irving

check-defs:
	@echo "==> Checking $(DEFS)"
	$(AXLE) check --environment $(ENV) - < $(DEFS)

check-gs:
	@echo "==> Checking $(GALESHAPLEY)"
	$(call cat_with_defs,$(GALESHAPLEY)) | $(AXLE) check --environment $(ENV) -

check-irving:
	@echo "==> Checking $(IRVING)"
	$(call cat_with_defs,$(IRVING)) | $(AXLE) check --environment $(ENV) -

# Fail with non-zero exit code if there are any errors (sorrys included).
check-strict:
	@echo "==> Strict check: all files"
	$(AXLE) check --environment $(ENV) --strict - < $(DEFS)
	$(call cat_with_defs,$(GALESHAPLEY)) | $(AXLE) check --environment $(ENV) --strict -
	$(call cat_with_defs,$(IRVING)) | $(AXLE) check --environment $(ENV) --strict -

# ── disprove ──────────────────────────────────────────────────────────────────
# Attempt to prove the *negation* of every theorem in a file.
# "failed to prove negation" = no counterexample found = positive evidence.
# "disproved_theorems: [...]" = a claim is wrong; revise it before proceeding.
# Timeout is per-file. Increase for complex goals: make disprove TIMEOUT=300

disprove: disprove-gs disprove-irving

disprove-gs:
	@echo "==> Disprove: $(GALESHAPLEY)"
	$(call cat_with_defs,$(GALESHAPLEY)) | $(AXLE) disprove --environment $(ENV) --timeout-seconds $(TIMEOUT) -

disprove-irving:
	@echo "==> Disprove: $(IRVING)"
	$(call cat_with_defs,$(IRVING)) | $(AXLE) disprove --environment $(ENV) --timeout-seconds $(TIMEOUT) -

# ── sorry2lemma ───────────────────────────────────────────────────────────────
# Extract every `sorry` placeholder (and unsolved error goals) into standalone
# top-level lemmas, making the remaining proof obligations explicit.
# Outputs: JSON metadata + the modified Lean source with extracted stubs.
# Target a specific file: make sorry2lemma FILE=HedonicGrouping/Irving.lean
# Target specific theorems: make sorry2lemma FILE=HedonicGrouping/Irving.lean NAMES=foo,bar

NAMES ?=

sorry2lemma:
	@echo "==> Extracting sorrys from $(FILE)"
	$(call cat_with_defs,$(FILE)) | $(AXLE) sorry2lemma --environment $(ENV) \
	    $(if $(NAMES),--names $(NAMES),) \
	    --reconstruct-callsite \
	    -

# ── repair ────────────────────────────────────────────────────────────────────
# Attempt to automatically repair broken or incomplete proofs.
# Tries terminal tactics (default: grind) to close open goals.
# Outputs the repaired Lean source; redirect to file to apply:
#   make repair FILE=HedonicGrouping/Irving.lean > Irving_repaired.lean
# Target specific theorems: make repair NAMES=rotation_eliminates_less_preferred

repair:
	@echo "==> Attempting proof repair on $(FILE)"
	$(call cat_with_defs,$(FILE)) | $(AXLE) repair-proofs --environment $(ENV) \
	    $(if $(NAMES),--names $(NAMES),) \
	    --terminal-tactics grind,simp,omega,decide \
	    -

# ── simplify ──────────────────────────────────────────────────────────────────
# Clean up tactic proofs: remove redundant steps, shorten proof blocks.
# Run this after all sorrys are closed. Outputs the simplified Lean source.
# Redirect to apply: make simplify-gs > GaleShapley_simplified.lean

simplify: simplify-gs simplify-irving

simplify-gs:
	@echo "==> Simplifying proofs in $(GALESHAPLEY)"
	$(call cat_with_defs,$(GALESHAPLEY)) | $(AXLE) simplify-theorems --environment $(ENV) -

simplify-irving:
	@echo "==> Simplifying proofs in $(IRVING)"
	$(call cat_with_defs,$(IRVING)) | $(AXLE) simplify-theorems --environment $(ENV) -

# ── extract ───────────────────────────────────────────────────────────────────
# Split each file into per-theorem .lean files with full dependency tracking.
# Output goes to EXTRACT_DIR (default: HedonicGrouping/extracted/).
# Use this to produce the publishable supplementary artifact.

extract:
	@echo "==> Extracting theorems from $(GALESHAPLEY) → $(EXTRACT_DIR)"
	$(call cat_with_defs,$(GALESHAPLEY)) | $(AXLE) extract-theorems --environment $(ENV) \
	    --output-dir $(EXTRACT_DIR) --force -
	@echo "==> Extracting theorems from $(IRVING) → $(EXTRACT_DIR)"
	$(call cat_with_defs,$(IRVING)) | $(AXLE) extract-theorems --environment $(ENV) \
	    --output-dir $(EXTRACT_DIR) --force -

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
