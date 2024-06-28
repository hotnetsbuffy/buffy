include "scheduler.dfy"

module Traffic refines Scheduler {
  method run_t ... {
    var cand := ibs.Length - 1;
    var i := 0;
    for i := 0 to ibs.Length invariant cand >= 0 && cand < ibs.Length{
      cand := i;
    }
    if backlog(ibs[cand]) > 0{
      var (ib, ob) := move(ibs[cand], obs[0]);
      ibs[cand] := ib;
      obs[0] := ob;
    }
  }
}