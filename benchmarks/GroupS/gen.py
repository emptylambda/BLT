#! /usr/bin/env python

import sys, os

def build(n, before, after, repeat, prefix, timeout=lambda k: 60*5):
    body = ""
    for i in range(1,n+1):
        body += repeat
    fname = "%s%02d.bpl" % (prefix, n)
    with open(fname, "w") as fp:
        fp.write(before + body + after)
    to = timeout(n)
    with open(fname.rstrip(".bpl") + ".timeout", "w") as fp:
        fp.write("%s" % str(to))

def simple_build(n, prefix, body, timeout=lambda k: 60*5):
    fname = "%s%02d.bpl" % (prefix, n)
    with open(fname, "w") as fp:
        fp.write(body)
    to = timeout(n)
    with open(fname.rstrip(".bpl") + ".timeout", "w") as fp:
        fp.write("%s" % str(to))


def sequential_ifs(n):
    before = """
const bar: int;
procedure main() returns ()
{
  var pos, neg, i: int;
  pos, neg, i :=  0, 0, 0;
"""
    after = """
  assert i == pos + neg;
}				
"""
    repeat = """
  if (i >= bar) { pos := pos + 1; i := i + 1; }
  else { neg := neg + 1; i := i + 1; }
"""
    build(n, before, after, repeat, "sif")

def sequential_assign(n):
    before = """
procedure main() returns()
{
   var x, n: int;
   x, n := 0, %s;
""" % str(n)
    after = """
   assert x == n;
}
"""
    repeat = """
   x := x + 1;
"""
    build(n, before, after, repeat, "sasgn")

def nested_ifs(n):
    base = """if (i >= bar) {
   pos, i := pos + 1, i + 1;
   %s
  } else {
   neg, i := neg + 1, i + 1;
   %s
  }
"""
    def rifs(k):
        if k == 1:
            return base % ("", "")
        else:
            return base % (rifs(k - 1), rifs(k - 1))
    before = """
const bar: int;
procedure main() returns ()
{
  var pos, neg, i: int;
  pos, neg, i :=  0, 0, 0;
"""
    after = """
  assert i == pos + neg;
}				
"""
    body = rifs(n)
    simple_build(n, "nifs", before + body + after)

def multivariables(n):
    before = """
procedure main() returns()
{
"""
    vs = ["x%03d" % k for k in range(1, n+1)]
    repeat = "\n".join(["  var %s: int;" % v for v in vs]) + "\n\n" + \
             "\n".join(["  %s := 1;" % v for v in vs])
    ending = "\n\n" + ("  assert %d == " % n) + " + ".join(["%s" % v for v in vs]) + ";"
    after = ending + """
}
"""
    body = before + repeat + after
    simple_build(n, "mvars", body)

if __name__ == "__main__":
    for i in range(10):
        nested_ifs(i+1)
    for i in range(21):
        sequential_ifs(i+1)
    for i in range(0,300,30):
        sequential_assign(i+1)
        multivariables(i+1)
