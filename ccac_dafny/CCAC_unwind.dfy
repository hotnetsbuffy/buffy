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

method {:axiom} Main(){
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
  //var losstrack := [];
  var tokens := 0;
  var time := 1;
  var sent := 0;
  var lost := 0;
  var seen_serviced := 0;
  var a, b, c, d;
    for i := 0 to (cwnd.Floor + 2)
      invariant 0 <= i <= cwnd.Floor + 2
      invariant |iba[2]| >= i  
    {
      iba[2] := iba[2] + [1];
    }
  iba[0] := [];
  iba[1] := [];
  oba[0] := [];
    a, b, c, d := CC.run_t(iba, oba, cwnd, sent, lost, seen_serviced);
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
    assert(seen_serviced == 0);
    ibb[0] := ibb[0] + oba[0];
    oba[0] := [];
    tokens, wastetrack, servicetrack := PathServer.run_ts(ibb, obb, tokens, wastetrack, servicetrack, time);
    iba[0] := iba[0] +  obb[1];
    obb[1] := [];
    ibc[0] := ibc[0] +  obb[2];
    obb[2] := [];
    DelayServer.run_t(ibc, obc, time);
    iba[1] := iba[1] + obc[0];
    obc[0] := [];
    time := time + 1;
    //another iteration
    a, b, c, d := CC.run_t(iba, oba, cwnd, sent, lost, seen_serviced);
    for i := 0 to (cwnd.Floor + 2)
      invariant 0 <= i <= cwnd.Floor + 2
      invariant |iba[2]| >= i  
      invariant |oba[0]| == b - sent
    {
      iba[2] := iba[2] + [1];
    }
    cwnd := a;
    sent := b;
    lost := c;
    seen_serviced := d;
    ibb[0] := ibb[0] + oba[0];
    oba[0] := [];
    tokens, wastetrack, servicetrack := PathServer.run_ts(ibb, obb, tokens, wastetrack, servicetrack, time);
    iba[0] := iba[0] +  obb[1];
    obb[1] := [];
    ibc[0] := ibc[0] +  obb[2];
    obb[2] := [];
    DelayServer.run_t(ibc, obc, time);
    iba[1] := iba[1] + obc[0];
    obc[0] := [];
    time := time + 1;
    //another iteration
    a, b, c, d := CC.run_t(iba, oba, cwnd, sent, lost, seen_serviced);
    for i := 0 to (cwnd.Floor + 2)
      invariant 0 <= i <= cwnd.Floor + 2
      invariant |iba[2]| >= i  
      invariant |oba[0]| == b - sent
    {
      iba[2] := iba[2] + [1];
    }
    cwnd := a;
    sent := b;
    lost := c;
    seen_serviced := d;
    ibb[0] := ibb[0] + oba[0];
    oba[0] := [];
    tokens, wastetrack, servicetrack := PathServer.run_ts(ibb, obb, tokens, wastetrack, servicetrack, time);
    iba[0] := iba[0] +  obb[1];
    obb[1] := [];
    ibc[0] := ibc[0] +  obb[2];
    obb[2] := [];
    DelayServer.run_t(ibc, obc, time);
    iba[1] := iba[1] + obc[0];
    obc[0] := [];
    time := time + 1;
        //another iteration
    a, b, c, d := CC.run_t(iba, oba, cwnd, sent, lost, seen_serviced);
    for i := 0 to (cwnd.Floor + 2)
      invariant 0 <= i <= cwnd.Floor + 2
      invariant |iba[2]| >= i  
      invariant |oba[0]| == b - sent
    {
      iba[2] := iba[2] + [1];
    }
    cwnd := a;
    sent := b;
    lost := c;
    seen_serviced := d;
    ibb[0] := ibb[0] + oba[0];
    oba[0] := [];
    tokens, wastetrack, servicetrack := PathServer.run_ts(ibb, obb, tokens, wastetrack, servicetrack, time);
    iba[0] := iba[0] +  obb[1];
    obb[1] := [];
    ibc[0] := ibc[0] +  obb[2];
    obb[2] := [];
    DelayServer.run_t(ibc, obc, time);
    iba[1] := iba[1] + obc[0];
    obc[0] := [];
    time := time + 1;
    //another iteration
    a, b, c, d := CC.run_t(iba, oba, cwnd, sent, lost, seen_serviced);
    for i := 0 to (cwnd.Floor + 2)
      invariant 0 <= i <= cwnd.Floor + 2
      invariant |iba[2]| >= i  
      invariant |oba[0]| == b - sent
    {
      iba[2] := iba[2] + [1];
    }
    cwnd := a;
    sent := b;
    lost := c;
    seen_serviced := d;
    ibb[0] := ibb[0] + oba[0];
    oba[0] := [];
    tokens, wastetrack, servicetrack := PathServer.run_ts(ibb, obb, tokens, wastetrack, servicetrack, time);
    iba[0] := iba[0] +  obb[1];
    obb[1] := [];
    ibc[0] := ibc[0] +  obb[2];
    obb[2] := [];
    DelayServer.run_t(ibc, obc, time);
    iba[1] := iba[1] + obc[0];
    obc[0] := [];
    time := time + 1;
    //another iteration
    a, b, c, d := CC.run_t(iba, oba, cwnd, sent, lost, seen_serviced);
    for i := 0 to (cwnd.Floor + 2)
      invariant 0 <= i <= cwnd.Floor + 2
      invariant |iba[2]| >= i  
      invariant |oba[0]| == b - sent
    {
      iba[2] := iba[2] + [1];
    }
    cwnd := a;
    sent := b;
    lost := c;
    seen_serviced := d;
    ibb[0] := ibb[0] + oba[0];
    oba[0] := [];
    tokens, wastetrack, servicetrack := PathServer.run_ts(ibb, obb, tokens, wastetrack, servicetrack, time);
    iba[0] := iba[0] +  obb[1];
    obb[1] := [];
    ibc[0] := ibc[0] +  obb[2];
    obb[2] := [];
    DelayServer.run_t(ibc, obc, time);
    iba[1] := iba[1] + obc[0];
    obc[0] := [];
    time := time + 1;
    //another iteration
    a, b, c, d := CC.run_t(iba, oba, cwnd, sent, lost, seen_serviced);
    for i := 0 to (cwnd.Floor + 2)
      invariant 0 <= i <= cwnd.Floor + 2
      invariant |iba[2]| >= i  
      invariant |oba[0]| == b - sent
    {
      iba[2] := iba[2] + [1];
    }
    cwnd := a;
    sent := b;
    lost := c;
    seen_serviced := d;
    ibb[0] := ibb[0] + oba[0];
    oba[0] := [];
    tokens, wastetrack, servicetrack := PathServer.run_ts(ibb, obb, tokens, wastetrack, servicetrack, time);
    iba[0] := iba[0] +  obb[1];
    obb[1] := [];
    ibc[0] := ibc[0] +  obb[2];
    obb[2] := [];
    DelayServer.run_t(ibc, obc, time);
    iba[1] := iba[1] + obc[0];
    obc[0] := [];
    time := time + 1;
    //another iteration
    a, b, c, d := CC.run_t(iba, oba, cwnd, sent, lost, seen_serviced);
    for i := 0 to (cwnd.Floor + 2)
      invariant 0 <= i <= cwnd.Floor + 2
      invariant |iba[2]| >= i  
      invariant |oba[0]| == b - sent
    {
      iba[2] := iba[2] + [1];
    }
    cwnd := a;
    sent := b;
    lost := c;
    seen_serviced := d;
    ibb[0] := ibb[0] + oba[0];
    oba[0] := [];
    tokens, wastetrack, servicetrack := PathServer.run_ts(ibb, obb, tokens, wastetrack, servicetrack, time);
    iba[0] := iba[0] +  obb[1];
    obb[1] := [];
    ibc[0] := ibc[0] +  obb[2];
    obb[2] := [];
    DelayServer.run_t(ibc, obc, time);
    iba[1] := iba[1] + obc[0];
    obc[0] := [];
    time := time + 1;
    assert(|wastetrack| == 7);
    assume(wastetrack == [0, 0, 0, 0, 0, 0, 0]);
    assume(servicetrack == [5, 10, 10, 10, 20, 20, 20]);
    assert(lost > 0);
    print("\n");

}

