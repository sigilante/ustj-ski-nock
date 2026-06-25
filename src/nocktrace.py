#!/usr/bin/env python3
"""
nocktrace -- a small-step Nock 4K rewriter that prints every reduction step,
with an SKI -> Nock {0,1,2} compiler front-end.

Two trace phases:
  A. compile expansion  -- expand the [[.]] compiler brackets one rule at a time,
                           keeping S/K/I as symbols, then substitute their formulas
  B. evaluation         -- reduce *[subject formula] one Nock rule per step to a noun

Endpoint is cross-checked against pinochle when available.

Expression representation:
  atom            : int
  cell            : ('C', head, tail)
  tap   *[s f]    : ('*', s, f)
  fas   /[ax n]   : ('/', ax, n)
  lus   +[x]      : ('+', x)
  tis   =[a b]    : ('=', a, b)
  wut   ?[x]      : ('?', x)
  meta  [[t]]     : ('M', ski_term)            (compile phase only)
  symbol S/K/I    : 'S' | 'K' | 'I'            (compile phase only)
  ski app (a b)   : ('@', a, b)                (ski terms only)
"""

# ---------------- combinator value formulas (pure 0/1/2) ----------------
C = lambda *xs: xs[0] if len(xs)==1 else ('C', xs[0], C(*xs[1:]))
SKI_FORMULA = {
    'I': C(0,1),
    'K': C(C(1,1), C(0,1)),
    'S': C(C(1,C(1,2)), C(1,C(0,1)), C(C(1,1),C(0,1))),
}

# ---------------- pretty printer (right-nest flattening) ----------------
def pp(e):
    if isinstance(e, int): return str(e)
    if isinstance(e, str): return e                      # symbol S/K/I
    t = e[0]
    if t == 'C':  return "[" + " ".join(pp(x) for x in flatten(e)) + "]"
    if t == '*':  return "*[" + " ".join(pp(x) for x in flatten(('C',e[1],e[2]))) + "]"
    if t == '/':  return "/[" + pp(e[1]) + " " + pp(e[2]) + "]"
    if t == '+':  return "+[" + pp(e[1]) + "]"
    if t == '=':  return "=[" + pp(e[1]) + " " + pp(e[2]) + "]"
    if t == '?':  return "?[" + pp(e[1]) + "]"
    if t == 'M':  return "[[" + ski_pp(e[1]) + "]]"
    raise ValueError(e)

def flatten(cell):                                       # ('C',a,('C',b,c)) -> [a,b,c]
    out=[]; x=cell
    while isinstance(x, tuple) and x[0]=='C':
        out.append(x[1]); x=x[2]
    out.append(x); return out

def ski_pp(t):
    if isinstance(t,str): return t
    if t[0]=='@': return ski_pp(t[1]) + " " + ski_pp(t[2])
    return str(t)

def is_noun(e):                                          # concrete: only ints and cells
    if isinstance(e,int): return True
    if isinstance(e,tuple) and e[0]=='C': return is_noun(e[1]) and is_noun(e[2])
    return False

# ---------------- SKI source parser ----------------
def parse_ski(s):
    toks=[]; i=0
    for ch in s:
        if ch in '()': toks.append(ch)
        elif ch.isspace(): pass
        elif ch in 'SKI': toks.append(ch)
        else: raise ValueError(f"bad char {ch!r}")
    pos=[0]
    def atom():
        if toks[pos[0]]=='(':
            pos[0]+=1; e=expr(); assert toks[pos[0]]==')'; pos[0]+=1; return e
        t=toks[pos[0]]; pos[0]+=1; return t
    def expr():
        e=atom()
        while pos[0]<len(toks) and toks[pos[0]]!=')':
            e=('@', e, atom())
        return e
    e=expr(); assert pos[0]==len(toks); return e

# ---------------- compile-expansion steps (phase A) ----------------
def to_meta(ski):  return ('M', ski)

def expand_meta_once(e):
    """Expand the leftmost [[.]] node by one compiler rule. Returns (new, rule) or None."""
    if isinstance(e, tuple) and e[0]=='M':
        t=e[1]
        if isinstance(t,str):                            # [[S]] = [1 S]
            return ('C', 1, t), f"[[{t}]] = [1 {t}]"
        if t[0]=='@':                                    # [[A B]] = [2 [[B]] [[A]]]
            A,B=t[1],t[2]
            return ('C', 2, ('C', ('M',B), ('M',A))), "[[A B]] = [2 [[B]] [[A]]]"
    # recurse
    if isinstance(e, tuple):
        for i in range(1,len(e)):
            r=expand_meta_once(e[i])
            if r: return e[:i]+(r[0],)+e[i+1:], r[1]
    return None

def substitute_symbols(e):
    if isinstance(e,str): return SKI_FORMULA[e]
    if isinstance(e,tuple): return tuple(substitute_symbols(x) if i>0 else e[0]
                                         for i,x in enumerate(e))
    return e

def has_symbol(e):
    if isinstance(e,str): return True
    if isinstance(e,tuple): return any(has_symbol(x) for x in e[1:])
    return False

# ---------------- small-step Nock evaluation (phase B) ----------------
def slot_step(ax, n):
    if ax==1: return n, "/[1 a] = a"
    if ax==2:
        assert isinstance(n,tuple) and n[0]=='C'; return n[1], "/[2 [a b]] = a"
    if ax==3:
        assert isinstance(n,tuple) and n[0]=='C'; return n[2], "/[3 [a b]] = b"
    if ax%2==0: return ('/',2,('/',ax//2,n)), f"/[{ax} n] = /[2 /[{ax//2} n]]"
    return ('/',3,('/',ax//2,n)), f"/[{ax} n] = /[3 /[{ax//2} n]]"

def reduce_once(e):
    """Reduce the leftmost-outermost redex by one rule. Returns (new, rule) or None."""
    if isinstance(e,(int,str)): return None
    t=e[0]

    if t=='*':
        s,f=e[1],e[2]
        if is_noun(f) and isinstance(f,tuple) and f[0]=='C':
            op=f[1]
            if isinstance(op,int):
                if op==0: return ('/', f[2], s), "Nock 0  *[a 0 b] = /[b a]"
                if op==1: return f[2], "Nock 1  *[a 1 b] = b"
                if op==2:
                    b,c=f[2][1],f[2][2]
                    return ('*', ('*',s,b), ('*',s,c)), "Nock 2  *[a 2 b c] = *[*[a b] *[a c]]"
                if op==3: return ('?', ('*',s,f[2])), "Nock 3  *[a 3 b] = ?[*[a b]]"
                if op==4: return ('+', ('*',s,f[2])), "Nock 4  *[a 4 b] = +[*[a b]]"
                if op==5:
                    b,c=f[2][1],f[2][2]
                    return ('=', ('*',s,b), ('*',s,c)), "Nock 5  *[a 5 b c] = =[*[a b] *[a c]]"
                if op==6:
                    b,cd=f[2][1],f[2][2]; c,d=cd[1],cd[2]
                    macro=('*', s, ('C',2,('C',('C',0,1),('C',2,('C',('C',1,c,d),
                          ('C',('C',1,0),('C',2,('C',('C',1,2,3),('C',('C',1,0),
                          ('C',4,('C',4,b)))))))))))
                    return macro, "Nock 6  (if/then/else macro)"
                if op==7:
                    b,c=f[2][1],f[2][2]
                    return ('*', ('*',s,b), c), "Nock 7  *[a 7 b c] = *[*[a b] c]"
                if op==8:
                    b,c=f[2][1],f[2][2]
                    return ('*', ('C',('*',s,b),s), c), "Nock 8  *[a 8 b c] = *[[*[a b] a] c]"
                # head is an atom op we don't expand here:
                raise NotImplementedError(f"opcode {op}")
            else:                                        # autocons: head is a cell
                return ('C', ('*',s,f[1]), ('*',s,f[2])), "cons  *[a [b c] d] = [*[a b c] *[a d]]"
        # formula not yet a literal cell -> reduce it first (descend)
    if t=='/':
        ax,n=e[1],e[2]
        if isinstance(ax,int):
            if ax==1 or (ax in (2,3) and is_noun(n) and isinstance(n,tuple) and n[0]=='C') or ax>3:
                return slot_step(ax,n)
    if t=='+':
        if is_noun(e[1]) and isinstance(e[1],int):
            return e[1]+1, "+   +[m] = m+1"
    if t=='=':
        if is_noun(e[1]) and is_noun(e[2]):
            return (0 if e[1]==e[2] else 1), "=   =[a a]=0  =[a b]=1"
    if t=='?':
        if is_noun(e[1]):
            return (0 if isinstance(e[1],tuple) else 1), "?   ?[cell]=0  ?[atom]=1"

    # no root redex: descend left-to-right
    for i in range(1,len(e)):
        r=reduce_once(e[i])
        if r: return e[:i]+(r[0],)+e[i+1:], r[1]
    return None

# ---------------- drivers ----------------
def trace(e, label="", show_rules=True, limit=10000):
    steps=[e]; rules=[]
    n=0
    while True:
        r=reduce_once(e)
        if r is None: break
        e,rule=r; steps.append(e); rules.append(rule); n+=1
        if n>limit: raise RuntimeError("step limit")
    width=max(len(pp(s)) for s in steps)
    for i,s in enumerate(steps):
        line=pp(s)
        if show_rules and i>0:
            print(f"  {line.ljust(width)}   {rules[i-1]}")
        else:
            print(f"  {line}")
    return steps[-1]

def expand_ski(src, subject, show_rules=True):
    ski=parse_ski(src)
    e=('*', subject, ('M', ski))
    print(f"# *[{subject} [[{src}]]]   compile expansion")
    print(f"  {pp(e)}")
    # phase A: meta expansion
    while True:
        r=expand_meta_once(e)
        if r is None: break
        e,rule=r
        print(f"  {pp(e)}   {rule}" if show_rules else f"  {pp(e)}")
    # substitute combinator formulas
    e=substitute_symbols(e)
    print(f"  {pp(e)}   substitute S,K,I formulas")
    print(f"\n# evaluation")
    final=trace(e, show_rules=show_rules)
    return final

def ground_value(src):
    """Fully compile an SKI term to its ground value-producing formula."""
    e=('M', parse_ski(src))
    while True:
        r=expand_meta_once(e)
        if r is None: break
        e=r[0]
    return substitute_symbols(e)

def expand_apply(src, arg):
    """Trace applying the value of `src` to `arg`, ending in the applied result."""
    val_formula=ground_value(src)
    # apply(value, arg) == *[arg value]; trace that directly on the computed value
    print(f"# applying val({src}) to {arg}   ( *[{arg} val({src})] )")
    val=run_to_noun(('*', 0, val_formula))         # compute the value first (closed)
    print(f"  val({src}) = {pp(val)}")
    print(f"\n# evaluation of *[{arg} {pp(val)}]")
    return trace(('*', arg, val))

def run_to_noun(e):
    while True:
        r=reduce_once(e)
        if r is None: return e
        e=r[0]

# ---------------- entry ----------------
if __name__=="__main__":
    import sys
    args = sys.argv[1:]
    if not args:
        print("Usage: nocktrace.py <SKI-term> <subject>")
        print("  e.g.: nocktrace.py S K K 42")
        sys.exit(1)
    try:
        subject = int(args[-1])
    except ValueError:
        print(f"Error: last argument must be an integer subject, got {args[-1]!r}")
        sys.exit(1)
    ski_src = " ".join(args[:-1])
    if not ski_src:
        print("Error: SKI term must be non-empty")
        sys.exit(1)

    print("="*72)
    print(f"(1)  *[{subject} [[{ski_src}]]]   -- produces the VALUE of {ski_src}")
    print("="*72)
    final = expand_ski(ski_src, subject)
    print(f"\n= {pp(final)}")

    print("\n"+"="*72)
    print(f"(2)  applying that value to {subject}")
    print("="*72)
    applied = expand_apply(ski_src, subject)
    print(f"\n= {pp(applied)}")

    # ---- cross-check endpoints against pinochle ----
    try:
        from pinochle import nock as pnock, parse as pparse
        gv = ground_value(ski_src)
        v_self = pnock(0, pparse(pp(gv)))
        applied_pin = pnock(subject, pparse(pp(run_to_noun(('*', 0, gv)))))
        print("\n"+"-"*72)
        print(f"pinochle: val({ski_src})            = {v_self}")
        print(f"pinochle: that value on {subject}      = {applied_pin}")
        print(f"agreement: value {'OK' if str(v_self)==pp(final) else 'MISMATCH'}, "
              f"application {'OK' if str(applied_pin)==pp(applied) else 'MISMATCH'}")
    except Exception as ex:
        print("pinochle cross-check skipped:", ex)
