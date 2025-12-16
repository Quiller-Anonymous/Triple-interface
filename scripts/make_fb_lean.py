#!/usr/bin/env python3
import sys, csv, textwrap, math

def emit_header(modname):
    return textwrap.dedent(f"""\
    /-!  AUTO-GENERATED: finite base witnesses.
          DO NOT EDIT BY HAND.  -/
    import Mathlib
    import Goldbach.Base.FiniteBaseDefs

    open Nat
    open Goldbach.Base

    namespace {modname}
    """)

def lemma_for_N(N, p, q):
    return textwrap.dedent(f"""\
    /-- Witness for {N} = {p}+{q}. -/
    lemma rep_{N} : GoldbachRep {N} :=
    by
      refine ⟨{p}, {q}, ?hp, ?hq, ?hsum⟩
      · decide
      · decide
      · decide
    """)

def base_for_N(N):
    return textwrap.dedent(f"""\
    /-- Single-point base on [{N},{N}]. -/
    lemma base_{N} : FiniteBaseOn {N} {N} :=
    by
      intro N' hE hlo hhi
      have h : N' = {N} := le_antisymm hhi hlo
      simpa [h] using rep_{N}
    """)

def glue_block(a,b,modname):
    # a,b even with a ≤ b and step 2
    return textwrap.dedent(f"""\
    /-- Assembled window [{a},{b}] by gluing singletons. -/
    lemma base_{a}_{b} : FiniteBaseOn {a} {b} :=
    by
      -- auto-glue chain produced below
      have h0 : FiniteBaseOn {a} {a} := base_{a}
    """)

def emit_footer(modname, X0):
    return textwrap.dedent(f"""\
    /-- Final assembled finite base up to {X0}. -/
    theorem finiteBaseUpTo_{X0} : FiniteBaseUpTo {X0} :=
    by
      -- the script writes `have ...` chain to a `hFinal` for [4,{X0}]
      exact base_4_{X0}

    end {modname}
    """)

def main():
    if len(sys.argv) != 5:
        print("usage: make_fb_lean.py <input.csv> <out.lean> <Mod.Name> <X0>", file=sys.stderr)
        sys.exit(2)

    csv_path, outlean, modname, X0s = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
    X0 = int(X0s)
    rows = []
    with open(csv_path, newline="") as f:
        rd = csv.DictReader(f)
        for r in rd:
            N,p,q = int(r["N"]), int(r["p"]), int(r["q"])
            if N % 2 == 0 and 4 <= N <= X0:
                rows.append((N,p,q))
    rows.sort()
    # sanity
    exp = list(range(4, X0+1, 2))
    got = [N for (N,_,_) in rows]
    if got != exp:
        missing = sorted(set(exp) - set(got))
        print(f"ERROR: csv missing {len(missing)} evens; e.g. {missing[:10]}", file=sys.stderr)
        sys.exit(3)

    with open(outlean, "w") as w:
        w.write(emit_header(modname))
        # emit witnesses and singletons
        for (N,p,q) in rows:
            w.write(lemma_for_N(N,p,q))
            w.write(base_for_N(N))

        # emit a glue chain in blocks of, say, 200 even numbers
        block = 200
        # start block
        current_lo = 4
        current_hi = current_lo
        w.write(glue_block(4, 4, modname))
        w.write("      have hb : FiniteBaseOn {0} {0} := base_{0}\n".format(4))
        w.write("      have hAgg : FiniteBaseOn {0} {0} := hb\n".format(4))
        # grow window
        for N in range(6, X0+1, 2):
            # glue hAgg ([4..N-2]) with singleton [N,N]
            w.write(textwrap.dedent(f"""\
                  have hN : FiniteBaseOn {N} {N} := base_{N}
                  have hAgg : FiniteBaseOn 4 {N} :=
                    FiniteBaseOn.union_even_cover (by decide) (by decide) (by decide)
                      (by decide) (by decide)
                      hAgg hN
            """))
        w.write("      exact hAgg\n\n")
        # finish file
        w.write(emit_footer(modname, X0))

if __name__ == "__main__":
    main()
