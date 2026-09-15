"""Causality-health metrics across every example. Writes only to tools/_metrics_out/.

    python tools/causality_metrics.py <tag> [example ...]
    FINSEM=weak python tools/causality_metrics.py weak

Reports, per example: |C~|, number of reported causes, how many check_formula
calls returned True, whether the ORIGINAL counterexample is recognised as a
violation, and the sizes of the reported causes. See STAGE0-FINDING.md.
"""
import os, sys, io, json, contextlib, traceback
from types import SimpleNamespace

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
HERE = os.path.dirname(os.path.abspath(__file__))
OUT  = os.path.join(HERE, "_metrics_out"); os.makedirs(OUT, exist_ok=True)
sys.path.insert(0, os.path.join(REPO, "explainhyper"))

FORMULAS = {
 "running_example": 'Forall (Forall (Implies (G (And (Eq (AP "li" 0) (AP "li" 1)) (Eq (AP "li" 0) (AP "li" 1)))) (G (And (Eq (AP "lo" 0) (AP "lo" 1)) (Eq (AP "ho" 0) (AP "ho" 1))))))',
 "security_in_and_out": 'Forall (Forall (Implies (G (Eq (AP "li" 0) (AP "li" 1))) (G (Eq (AP "lo" 0) (AP "lo" 1)))))',
 "drone_example_1": 'Forall (Forall (Implies (G (Eq (AP "bound" 0) (AP "bound" 1))) (G (Eq (AP "emergency" 0) (AP "emergency" 1)))))',
 "drone_example_2": 'Forall (Forall (Implies (G (And (Eq (AP "up" 0) (AP "up" 1)) (Eq (AP "bound" 0) (AP "bound" 1)))) (G (And (Eq (AP "increase" 0) (AP "increase" 1)) (Eq (AP "emergency" 0) (AP "emergency" 1))))))',
 "asymmetric_arbiter": 'Forall (Forall (Implies (G (And (Eq (AP "req_0" 0) (AP "req_0" 1)) (Eq (AP "req_1" 0) (AP "req_1" 1)))) (G (And (Eq (AP "grant_0" 0) (AP "grant_0" 1)) (Eq (AP "grant_1" 0) (AP "grant_1" 1))))))',
 "asymmetric_arbiter_19": 'Forall (Forall (Implies (G (And (Eq (AP "req_0" 0) (AP "req_0" 1)) (Eq (AP "req_1" 0) (AP "req_1" 1)))) (G (And (Eq (AP "grant_0" 0) (AP "grant_0" 1)) (Eq (AP "grant_1" 0) (AP "grant_1" 1))))))',
 "triple_forall": 'Forall (Forall (Forall (G (Neg (Or (AP "out" 0) (Or (AP "out" 1) (AP "out" 2)))))))',
 "simple_buffer": 'Forall (Forall (G (Eq (AP "out" 0) (AP "out" 1))))',
 "leaky_mux": 'Forall (Forall (Implies (G (And (Eq (AP "a" 0) (AP "a" 1)) (Eq (AP "b" 0) (AP "b" 1)))) (G (Eq (AP "out" 0) (AP "out" 1)))))',
}

def probe(name):
    import explain_hyper
    exdir = os.path.join(REPO, "examples", name)
    os.chdir(exdir)
    args = SimpleNamespace(aag=os.path.join(exdir, name+".aag"), cex=os.path.join(exdir, name+".cex"),
                           f=FORMULAS[name], outName=os.path.join(OUT, name+"_probe"),
                           stateMachine=os.path.join(exdir, name+".dot"),
                           finiteSemantics=os.environ.get("FINSEM","strong"))
    real_check, real_min = explain_hyper.check_formula, explain_hyper.minimality
    st = {"checked": False, "orig": None, "orig_lasso": None, "ctilde": None,
          "v": [], "cf_lasso": set()}
    def tc(f, tr_, a, fold, aps, ls, nt=2):
        v = real_check(f, tr_, a, fold, aps, ls, nt); st["v"].append(v)
        st["cf_lasso"].add(bool(tr_.is_liveness())); return v
    def tm(i, cause, orig, f, fold, a, circ, aps, ls, nt):
        if not st["checked"]:
            st["checked"]=True; st["ctilde"]=len(cause); st["orig_lasso"]=bool(orig.is_liveness())
            st["orig"]=real_check(f, orig, a, fold, aps, ls, nt)
        return real_min(i, cause, orig, f, fold, a, circ, aps, ls, nt)
    explain_hyper.check_formula, explain_hyper.minimality = tc, tm
    buf = io.StringIO(); err=None; causes=None; ncauses=None
    try:
        with contextlib.redirect_stdout(buf): explain_hyper.actual_causality(args)
    except Exception as e:
        err = f"{type(e).__name__}: {e}"
    finally:
        explain_hyper.check_formula, explain_hyper.minimality = real_check, real_min
    for line in buf.getvalue().splitlines():
        if line.startswith("All minimal causes"): causes = line.split(": ",1)[1]
        if line.startswith("Number of minimal causes"): ncauses = int(line.rsplit(": ",1)[1])
    sizes = None
    if causes:
        try: sizes = sorted({len(c) for c in eval(causes)})
        except Exception: pass
    return {"example":name,"error":err,"orig_is_lasso":st["orig_lasso"],
            "check_original":st["orig"],"ctilde":st["ctilde"],
            "calls":len(st["v"]),"true":sum(st["v"]),"false":len(st["v"])-sum(st["v"]),
            "cf_lasso_seen":sorted(st["cf_lasso"]),"n_causes":ncauses,"cause_sizes":sizes,
            "degenerate": (ncauses is not None and ncauses==st["ctilde"] and sum(st["v"])==0)}

if __name__ == "__main__":
    tag = sys.argv[1]; names = sys.argv[2:] or list(FORMULAS)
    rows=[]
    for n in names:
        try: r = probe(n)
        except Exception as e: r = {"example":n,"error":f"HARNESS {type(e).__name__}: {e}"}
        rows.append(r)
        print(f"{r['example']:24} ctilde={r.get('ctilde')!s:5} causes={r.get('n_causes')!s:5} "
              f"true={r.get('true')!s:4} orig={r.get('check_original')!s:6} "
              f"sizes={r.get('cause_sizes')!s:10} degen={r.get('degenerate')!s:6} {r.get('error') or ''}")
    p = os.path.join(HERE, f"metrics-{tag}.json")
    json.dump(rows, open(p,"w"), indent=1); print("\nwrote", p)
