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

  /*method run_ts (ibs: array<Buf>, obs: array<Buf>) 
  {
    //ibs[0] is loss, ibs[1] is serviced,ibs[2] is input obs[0] is arrived, 
    var recent_loss := 0;
    var recent_service := 0;
    for i := 1 to c {
      tokenqueue := tokenqueue + [time];
    }
    for j := 1 to |tokenqueue| {
      if (|tokenqueue| > 0 && tokenqueue[0] < time - slack) {
        tokenqueue := tokenqueue[1..];
      }
    }
    var movable_bytes := min(|tokenqueue|, backlog(ibs[0]) - |delay|);
    var delay_time :| 0 < delay_time < 2;
    var timeout := false;
    recent_loss := backlog(ibs[0]);
    ibs[0] := [];
// TODO: empty loss
    recent_service := head(ibs[1]);
    if (in_flight == recent_loss) {
        timeout := true;
    }
    for j := 1 to movable_bytes {
      tokenqueue := tokenqueue[1..];
      delay := delay + [delay_time + time];
    }
    var lost := 0;
    if(|tokenqueue| == 0 && backlog(ibs[0]) - movable_bytes - |delay| > loss_threshold) {
      var lost_bytes := (backlog(ibs[0]) - loss_threshold);
      ibs[0], obs[1] := moven(ibs[0], obs[1], lost_bytes);
    }
    var move_bytes := 0;
    for i := 0 to |delay| {
      if(delay[i] < time) {
      move_bytes := move_bytes + 1;
      var (ib, ob) := move(ibs[0], obs[0]);
      ibs[0] := ib;
      obs[0] := ob;
            //delay.remove(ele);

      }
    }
    time := time + 1;
  }*/

}