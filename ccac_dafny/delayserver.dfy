include "buffer.dfy"

module DelayServer {
  const delay_time := 1
  import opened Buffer
  method run_t (ibs: array<Buf>, obs: array<Buf>, time: int) 
    requires ibs.Length > 0
    requires obs.Length > 0
    modifies ibs
    modifies obs
  {
    var total := backlog(ibs[0]);
    for i := 0 to total {
      if((head(ibs[0]) + delay_time) >= time) {
        var (ib, ob) := move(ibs[0], obs[0]);
        ibs[0] := ib;
        obs[0] := ob;
      }
    }
  }

}