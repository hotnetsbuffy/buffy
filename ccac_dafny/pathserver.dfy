include "scheduler.dfy"



module PathServer {
    import opened Buffer
    const c := 5
    const slack := 2
    const loss_threshold := 10
    const delay := 2
function min(a: int, b: int): int
{ /* body must be an expression */
if a < b then a else b
}

function max(a: int, b: int): int
{ /* body must be an expression */
if a > b then a else b
}

  method gettokenamount(start: int, thresh: int, size: int ) returns (y : int) 
requires size >= 0
ensures y >= 0
ensures y <= size
ensures start + size >= thresh ==> y >= thresh - start
ensures start + size <= thresh ==> y == size
{
  var t :| 0 <= t <= size;
  if  (start + size <= thresh) {
    return size;
  }
  else if (start <= thresh) {
    var x :| 0 <= x <= start + size - thresh;
    return x + thresh - start;

  }
  return t;
}
predicate sorted(s: seq<int>)
{
    forall i :: 1 <= i < |s| ==> s[i] >= s[i-1]
}
predicate sorted2(s: seq<int>)
{
    forall i :: 1 <= i < |s| ==> (c * i) - s[i] >= c * (i - 1) - s[i-1]
}

predicate lessthanc(s: seq<int>)
{
    forall i :: 0 <= i < |s| ==> s[i] <= c * (i + 1)
}

predicate bothlessthanc(s1: seq<int>, s2: seq<int>)
{
    |s1| == |s2| && forall i :: 0 <= i < |s1| ==> s1[i] + s2[i] <= c * (i + 1)
}

predicate sameforn(s1: seq<int>, s2: seq<int>, n: int )
{
   |s1| >= n && |s2| >= n && forall i :: 0 <= i < n ==> s1[i] == s2[i]
}



predicate greaterthan0(s: seq<int>)
{
    forall i :: 0 <= i < |s| ==> s[i] >= 0
}


  method run_ts (ibs: array<Buf>, obs: array<Buf>, tokens: int, wastetrack: seq<int>, servicetrack: seq<int>, time: int)  returns (x : int, y : seq<int>, z  : seq<int>)
    requires ibs.Length >= 1
    requires obs.Length >= 3
    modifies ibs
    modifies obs
    requires |wastetrack| == time - 1
    requires |servicetrack| == time - 1
    requires time >= 1
    requires sorted(wastetrack)
    requires sorted2(wastetrack)
    requires lessthanc(wastetrack) 
    requires sorted(servicetrack)
    requires lessthanc(servicetrack)
    requires greaterthan0(servicetrack)
    requires greaterthan0(wastetrack)
    requires bothlessthanc(servicetrack, wastetrack)
    requires time == 1 ==> tokens == 0
    requires time > 1 ==> tokens == c * (time - 1) - wastetrack[time - 2] - servicetrack[time - 2]
    ensures sorted(y)
    ensures sorted(z)
    ensures lessthanc(z)
    ensures lessthanc(y)
    ensures sorted2(y)
    ensures greaterthan0(z)
    ensures greaterthan0(y)
    ensures bothlessthanc(y, z)
    ensures |y| == time
    ensures |z| == time
    ensures time > 1 ==> x == tokens + c - y[time - 1] + wastetrack[time - 2] - z[time - 1] + servicetrack[time - 2]
    ensures x == c * time - y[time - 1] - z[time - 1]
    ensures time > 1 ==> sameforn(wastetrack, y, time - 1)
    ensures time > 1 ==> sameforn(servicetrack, z, time - 1)
    ensures tokens + c <= backlog(ibs[0]) && time > 1 ==> y[time - 1] - y[time - 2] == 0
    ensures tokens + c <= backlog(ibs[0]) && time == 1 ==> y[time - 1] == 0
  {
    //ibs[0] is loss, ibs[1] is serviced,ibs[2] is input obs[0] is arrived, 
    var recent_loss := 0;
    var recent_service := 0;
    var addamount := gettokenamount(tokens, backlog(ibs[0]), c);
    assert tokens + c >= backlog(ibs[0]) ==> addamount + tokens >= backlog(ibs[0]) ;
    var wasteamount := c - addamount;
    var lowerbound := 0;
    if (time >= delay) {
        lowerbound := max(0, c * (time - delay) - wastetrack[time - delay]);
    }
    var wasteadd := wasteamount;
    if(|wastetrack| > 0) {
      wasteadd := wastetrack[|wastetrack| - 1] + wasteamount;
    }
    var upperbound := (c * time) - wasteadd;
    assert(wasteamount <= c);
    assert (addamount <= c);
    assert(lowerbound <= upperbound);
    assert(wasteadd >= 0);
    var servicetotal :| lowerbound <= servicetotal <= upperbound;
    print(lowerbound);
    print(" ");
    print(upperbound);
    print(" ");
    print(wasteamount);
    print(" ");
    print(servicetotal);

    if (time > 1 && servicetotal <= servicetrack[|servicetrack| - 1]) {
      servicetotal := servicetrack[|servicetrack| - 1];
    }
    var sub := 0;
    if(time > 1) {
      sub := servicetrack[|servicetrack| - 1];
    }
    var serviceincr := servicetotal - sub;
    print(" ");
    print(serviceincr);
    assert(servicetotal >= sub);
    assert(upperbound <= c * time);
    assert tokens + c <= backlog(ibs[0]) ==> wasteamount == 0;
    var start := ibs[0];
    ghost var initial := |start|;
    for j := 0 to serviceincr 
        invariant 0 <= j <= serviceincr
        invariant backlog(start) >= 0
        invariant backlog(start) >= initial - j - 1
        invariant |start| == 0 ==> backlog(start) <= initial 
        invariant |start| > 0 ==> |start| <= initial - j
    {
        ghost var initial := |ibs[0]|;
        var (ib, ob) := move(start, obs[0]);
        assert(|start| > 0 ==> |start| >= |ib|);
        start := ib;
        obs[0] := ob;
        obs[2] := obs[2] + [time];
    }
    ibs[0] := start;
    assert tokens + c <= backlog(ibs[0]) + serviceincr ==> wasteamount == 0;
    assert(addamount >= 0);
    var lost := 0;
    var newtokens := tokens + addamount - serviceincr;
    if(backlog(ibs[0]) - newtokens > loss_threshold) {
      var lost_bytes := (backlog(ibs[0]) - loss_threshold);
      ibs[0], obs[1] := moven(ibs[0], obs[1], lost_bytes);
      lost := lost_bytes;
    }
    return newtokens, 
    if time == 1 then [wasteamount] else wastetrack + [wastetrack[|wastetrack| - 1] + wasteamount], 
    if time == 1 then [servicetotal] else servicetrack + [servicetotal];
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