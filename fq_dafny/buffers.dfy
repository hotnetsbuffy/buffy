include "lib.dfy"

class Buffers {
  var bufs: array<seq<int>>
  var cdeq: array<int>

  constructor()
    ensures fresh(bufs)
    ensures fresh(cdeq)
    ensures valid()
    ensures forall i :: 0 <= i && i < cdeq.Length ==> cdeq[i] == 0
    ensures forall i :: 0 <= i && i < bufs.Length ==> bufs[i] == []
    ensures forall i :: 0 <= i && i < bufs.Length ==> |bufs[i]| == 0
  {
    this.bufs := new Buf[NUM_IN_BUFS + 1](_ => []);
    this.cdeq := new int[NUM_IN_BUFS](_ => 0);
  }

  predicate valid()
    reads this
    reads bufs
    reads cdeq
  {
    bufs.Length == NUM_IN_BUFS + 1
    && cdeq.Length == NUM_IN_BUFS
    && forall i :: 0 <= i && i < cdeq.Length ==> cdeq[i] >= 0
  }

  function backlog(i: BufIdx): int
    reads this
    reads bufs
    reads cdeq
    requires valid()
    requires valid_bi(i)
  {
    |bufs[i]|
  }

  function head(i: BufIdx): Pkt
    reads this
    reads bufs
    reads cdeq
    requires valid()
    requires valid_bi(i)
    requires backlog(i) > 0
  {
    bufs[i][0]
  }

  function tail(i: BufIdx): Buf
    reads this
    reads bufs
    reads cdeq
    requires valid()
    requires valid_bi(i)
    requires backlog(i) > 0
  {
    bufs[i][1..]
  }

  method enq(i: BufIdx, pkt: Pkt)
    requires valid_bi(i)
    requires valid()
    modifies bufs
    ensures bufs[i] == old(bufs[i]) + [pkt]
    ensures bufs == old(bufs)
    ensures backlog(i) == old(backlog(i)) + 1
    ensures valid()
    ensures forall j :: j >= 0 && j < bufs.Length && i != j ==> bufs[j] == old(bufs[j])
    ensures (forall j :: (j >= 0 && j < NUM_IN_BUFS && i != j ) ==>
                           (backlog(j) == old(backlog(j))))
  {
    bufs[i] := bufs[i] + [pkt];
  }

  method move(i: BufIdx, j: BufIdx)
    requires valid_bi(i)
    requires j == OUT_BUF_IDX
    requires valid()
    requires backlog(i) > 0
    requires i != j
    modifies bufs
    modifies cdeq
    ensures valid()
    ensures bufs[i] == old(tail(i))
    ensures bufs[j] == old(bufs[j]) + [old(head(i))]
    ensures forall k :: k >= 0 && k < bufs.Length && k != i && k != j ==> bufs[k] == old(bufs[k])
    ensures forall k :: 0 <= k && k < NUM_IN_BUFS &&  k != i ==>
                          old(cdeq[k]) == cdeq[k]
    ensures old(cdeq[i]) + 1 == cdeq[i]
  {
    var h := head(i);
    bufs[i] := tail(i);
    bufs[j] := bufs[j] + [h];
    cdeq[i] := cdeq[i] + 1;
  }
}
