include "buffer.dfy"
include "sp.dfy"
include "traffic.dfy"
include "pathserver.dfy"
include "CCA.dfy"
include "delayserver.dfy"
import CC = CCA
import TR = Traffic 
import SP = StrictPriority
const T := 10


//method flush(ob: Buf, ib: Buf)
// method flush(ob: array<Buf>, oi: int, ib: array<Buf>, ii: int)

method Main(){
  var iba := new Buf[3];
  var oba := new Buf[1];
  var ibb := new Buf[1];
  var obb := new Buf[3];

  var ibc := new Buf[1];
  var obc := new Buf[1];
  var cwnd := 10.0;
  var in_flight := 0;
  var wastetrack := [];
  var servicetrack := [];
  var tokens := 0;
  var time := 1;
  var sent := 0;
  var lost := 0;
  var seen_serviced := 0;
  for t := 1 to 100 
    invariant 1 <= t <= 101
    invariant backlog(iba[2]) >= t - 1 
    {
    iba[2] := iba[2] + [1];
  }
  assert(backlog(iba[2]) > 98);
  oba[0] := [];
  iba[1] := [];
  iba[0] := [];
  for t := 1 to T
    invariant 1 <= t <= T
    invariant |wastetrack| == time - 1
    invariant |servicetrack| == time - 1
    invariant PathServer.sorted(wastetrack)
    invariant PathServer.sorted2(wastetrack)
    invariant PathServer.lessthanc(wastetrack)
    invariant PathServer.sorted(servicetrack)
    invariant PathServer.greaterthan0(servicetrack)
    invariant PathServer.greaterthan0(wastetrack)
    invariant PathServer.greaterthan0(wastetrack)
    invariant PathServer.bothlessthanc(wastetrack, servicetrack)
    invariant cwnd.Floor >= 0
    invariant |iba[2]| >= cwnd.Floor + 1
    invariant time == 1 ==> tokens == 0
    invariant time > 1 ==> tokens == PathServer.c * (time - 1) - wastetrack[time - 2] - servicetrack[time - 2]
    invariant |oba[0]| == 0
    //invariant sent == lost + seen_serviced + |ibb[0]| + |ibc[0]| + |iba[1]| + |iba[0]| 
    invariant lost >= 0
    invariant seen_serviced >= 0
    invariant sent >= 0
   {
    var a, b, c, d := CC.run_t(iba, oba, cwnd, sent, lost, seen_serviced);
    assert(|oba[0]| == b - sent);
    for i := 0 to (cwnd.Floor + 2)
      invariant 0 <= i <= cwnd.Floor + 2
      invariant |iba[2]| >= i  
      invariant |oba[0]| == b - sent
    {
      iba[2] := iba[2] + [1];
    }
    assert(|oba[0]| == b - sent);
    cwnd := a;
    sent := b;
    lost := c;
    seen_serviced := d;
    ibb[0] := ibb[0] + oba[0];
    oba[0] := [];
    print(ibb[0]);
    tokens, wastetrack, servicetrack := PathServer.run_ts(ibb, obb, tokens, wastetrack, servicetrack, time);
    iba[0] := iba[0] +  obb[1];
    obb[1] := [];
    ibc[0] := ibc[0] +  obb[2];
    obb[2] := [];
    print(ibc[0]);
    DelayServer.run_t(ibc, obc, time);
    iba[1] := iba[1] + obc[0];
    obc[0] := [];
    time := time + 1;
    print(servicetrack);
    print(wastetrack);
    print(in_flight);
    print(in_flight);
    print("\n");
  }
  //print(ibb[0]);
  //print(iba[2]);
  //print(|iba[2]|);
}

