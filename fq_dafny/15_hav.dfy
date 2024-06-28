include "buffers.dfy"
include "lib.dfy"

const T := 15

function count_non_empty(s: seq<int>): int
  requires |s| == T
{
  btoi(s[0] > 1)
  + btoi(s[1] > 0)
  + btoi(s[2] > 0)
  + btoi(s[3] > 0)
  + btoi(s[4] > 0)
  + btoi(s[5] > 0)
  + btoi(s[6] > 0)
  + btoi(s[7] > 0)
  + btoi(s[8] > 0)
  + btoi(s[9] > 0)
  + btoi(s[10] > 0)
  + btoi(s[11] > 0)
  + btoi(s[12] > 0)
  + btoi(s[13] > 0)
  + btoi(s[14] > 0)
}

predicate alternate_traffic(s: seq<int>)
  requires |s| == T
{
  s[0] == 0
  && s[1] == 0
  && s[2] > 0
  && s[3] == 0
  && s[4] > 0
  && s[5] == 0
  && s[6] > 0
  && s[7] == 0
  && s[8] > 0
  && s[9] == 0
  && s[10] > 0
  && s[11] == 0
  && s[12] > 0
  && s[13] == 0
  && s[14] > 0
}

predicate wl(i0:seq<int>, i1:seq<int>, i2: seq<int>)
  requires |i0| == |i1| == |i2| == T
{
  count_non_empty(i1) >= T
  && count_non_empty(i2) >= T
  // && alternate_traffic(i0)
  && count_non_empty(i0) >= T
}


predicate query(cdeq0: MetricStream)
  requires |cdeq0| == T
{
  cdeq0[T-1] >= 7
}


method Main(){
  var bufs := new Buffers();

  var c00, c01, c02, c03, c04, c05, c06, c07, c08, c09, c010, c011, c012, c013, c014:int := *,*,*,*,*,*,*,*,*,*,*,*,*,*,*;
  var c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c110, c111, c112, c113, c114:int := *,*,*,*,*,*,*,*,*,*,*,*,*,*,*;
  var c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c210, c211, c212, c213, c214:int := *,*,*,*,*,*,*,*,*,*,*,*,*,*,*;

  var nq: seq<int> := [];
  var oq: seq<int> := [];
  var i0: seq<int> := [c00, c01, c02, c03, c04, c05, c06, c07, c08, c09, c010, c011, c012, c013, c014];
  var i1: seq<int> := [c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c110, c111, c112, c113, c114];
  var i2: seq<int> := [c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c210, c211, c212, c213, c214];
  var cdeq0: MetricStream := [];

  assume {:axiom} wl(i0, i1, i2);

  var t := 0;

  // ------ Loop Step Begin ------
  {
    {
      var i: int;
      var buf: int;

      i := 0;
      buf := i0[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
        if buf > 1 {bufs.enq(i, pkt);}
      }

      i := 1;
      buf := i1[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
        if buf > 1 {bufs.enq(i, pkt);}
      }

      i := 2;
      buf := i2[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
        if buf > 1 {bufs.enq(i, pkt);}
      }
    }

    {
      var i: int;
      i := 0;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 1;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 2;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }
    }

    {
      var i: int;
      var dequeued: bool;

      i := 0;
      dequeued := false;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 1;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 2;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

    }

    cdeq0 := cdeq0 + [bufs.cdeq[0]];
    t := t + 1;
  }
  // assert cdeq0[t - 1] == 0;
  // ------ Loop Step End ------

  // ------ Loop Step Begin ------
  {
    {
      var i: int;
      var buf: int;

      i := 0;
      buf := i0[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 1;
      buf := i1[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 2;
      buf := i2[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }
    }

    {
      var i: int;
      i := 0;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 1;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 2;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }
    }

    {
      var i: int;
      var dequeued: bool;

      i := 0;
      dequeued := false;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 1;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 2;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

    }

    cdeq0 := cdeq0 + [bufs.cdeq[0]];
    t := t + 1;
  }
  // assert cdeq0[t - 1] == 0;
  // ------ Loop Step End ------

  // ------ Loop Step Begin ------
  {
    {
      var i: int;
      var buf: int;

      i := 0;
      buf := i0[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 1;
      buf := i1[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 2;
      buf := i2[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }
    }

    {
      var i: int;
      i := 0;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 1;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 2;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }
    }

    {
      var i: int;
      var dequeued: bool;

      i := 0;
      dequeued := false;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 1;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 2;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

    }

    cdeq0 := cdeq0 + [bufs.cdeq[0]];
    t := t + 1;
  }
  // assert cdeq0[t - 1] == 1;
  // ------ Loop Step End ------

  // ------ Loop Step Begin ------
  {
    {
      var i: int;
      var buf: int;

      i := 0;
      buf := i0[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 1;
      buf := i1[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 2;
      buf := i2[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }
    }

    {
      var i: int;
      i := 0;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 1;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 2;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }
    }

    {
      var i: int;
      var dequeued: bool;

      i := 0;
      dequeued := false;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 1;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 2;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

    }

    cdeq0 := cdeq0 + [bufs.cdeq[0]];
    t := t + 1;
  }
  // assert cdeq0[t - 1] == 1;
  // ------ Loop Step End ------

  // ------ Loop Step Begin ------
  {
    {
      var i: int;
      var buf: int;

      i := 0;
      buf := i0[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 1;
      buf := i1[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 2;
      buf := i2[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }
    }

    {
      var i: int;
      i := 0;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 1;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 2;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }
    }

    {
      var i: int;
      var dequeued: bool;

      i := 0;
      dequeued := false;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 1;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 2;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

    }

    cdeq0 := cdeq0 + [bufs.cdeq[0]];
    t := t + 1;
  }
  // assert cdeq0[t - 1] == 2;
  // ------ Loop Step End ------

  // ------ Loop Step Begin ------
  {
    {
      var i: int;
      var buf: int;

      i := 0;
      buf := i0[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 1;
      buf := i1[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 2;
      buf := i2[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }
    }

    {
      var i: int;
      i := 0;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 1;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 2;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }
    }

    {
      var i: int;
      var dequeued: bool;

      i := 0;
      dequeued := false;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 1;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 2;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

    }

    cdeq0 := cdeq0 + [bufs.cdeq[0]];
    t := t + 1;
  }
  // assert cdeq0[t - 1] == 2;
  // ------ Loop Step End ------

  // ------ Loop Step Begin ------
  {
    {
      var i: int;
      var buf: int;

      i := 0;
      buf := i0[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 1;
      buf := i1[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 2;
      buf := i2[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }
    }

    {
      var i: int;
      i := 0;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 1;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 2;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }
    }

    {
      var i: int;
      var dequeued: bool;

      i := 0;
      dequeued := false;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 1;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 2;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

    }

    cdeq0 := cdeq0 + [bufs.cdeq[0]];
    t := t + 1;
  }
  // assert cdeq0[t - 1] == 3;
  // ------ Loop Step End ------

  // ------ Loop Step Begin ------
  {
    {
      var i: int;
      var buf: int;

      i := 0;
      buf := i0[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 1;
      buf := i1[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 2;
      buf := i2[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }
    }

    {
      var i: int;
      i := 0;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 1;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 2;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }
    }

    {
      var i: int;
      var dequeued: bool;

      i := 0;
      dequeued := false;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 1;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 2;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

    }

    cdeq0 := cdeq0 + [bufs.cdeq[0]];
    t := t + 1;
  }
  // assert cdeq0[t - 1] == 3;
  // ------ Loop Step End ------

  // ------ Loop Step Begin ------
  {
    {
      var i: int;
      var buf: int;

      i := 0;
      buf := i0[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 1;
      buf := i1[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 2;
      buf := i2[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }
    }

    {
      var i: int;
      i := 0;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 1;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 2;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }
    }

    {
      var i: int;
      var dequeued: bool;

      i := 0;
      dequeued := false;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 1;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 2;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

    }

    cdeq0 := cdeq0 + [bufs.cdeq[0]];
    t := t + 1;
  }
  // assert cdeq0[t - 1] == 3;
  // ------ Loop Step End ------

  // ------ Loop Step Begin ------
  {
    {
      var i: int;
      var buf: int;

      i := 0;
      buf := i0[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 1;
      buf := i1[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 2;
      buf := i2[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }
    }

    {
      var i: int;
      i := 0;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 1;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 2;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }
    }

    {
      var i: int;
      var dequeued: bool;

      i := 0;
      dequeued := false;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 1;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 2;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

    }

    cdeq0 := cdeq0 + [bufs.cdeq[0]];
    t := t + 1;
  }
  // assert cdeq0[t - 1] == 3;
  // ------ Loop Step End ------

  // ------ Loop Step Begin ------
  {
    {
      var i: int;
      var buf: int;

      i := 0;
      buf := i0[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 1;
      buf := i1[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 2;
      buf := i2[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }
    }

    {
      var i: int;
      i := 0;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 1;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 2;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }
    }

    {
      var i: int;
      var dequeued: bool;

      i := 0;
      dequeued := false;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 1;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 2;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

    }

    cdeq0 := cdeq0 + [bufs.cdeq[0]];
    t := t + 1;
  }
  // assert cdeq0[t - 1] == 3;
  // ------ Loop Step End ------


  // ------ Loop Step Begin ------
  {
    {
      var i: int;
      var buf: int;

      i := 0;
      buf := i0[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 1;
      buf := i1[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 2;
      buf := i2[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }
    }

    {
      var i: int;
      i := 0;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 1;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 2;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }
    }

    {
      var i: int;
      var dequeued: bool;

      i := 0;
      dequeued := false;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 1;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 2;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

    }

    cdeq0 := cdeq0 + [bufs.cdeq[0]];
    t := t + 1;
  }
  // assert cdeq0[t - 1] == 3;
  // ------ Loop Step End ------


  // ------ Loop Step Begin ------
  {
    {
      var i: int;
      var buf: int;

      i := 0;
      buf := i0[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 1;
      buf := i1[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 2;
      buf := i2[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }
    }

    {
      var i: int;
      i := 0;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 1;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 2;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }
    }

    {
      var i: int;
      var dequeued: bool;

      i := 0;
      dequeued := false;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 1;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 2;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

    }

    cdeq0 := cdeq0 + [bufs.cdeq[0]];
    t := t + 1;
  }
  // assert cdeq0[t - 1] == 3;
  // ------ Loop Step End ------

  // ------ Loop Step Begin ------
  {
    {
      var i: int;
      var buf: int;

      i := 0;
      buf := i0[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 1;
      buf := i1[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 2;
      buf := i2[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }
    }

    {
      var i: int;
      i := 0;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 1;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 2;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }
    }

    {
      var i: int;
      var dequeued: bool;

      i := 0;
      dequeued := false;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 1;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 2;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

    }

    cdeq0 := cdeq0 + [bufs.cdeq[0]];
    t := t + 1;
  }
  // assert cdeq0[t - 1] == 3;
  // ------ Loop Step End ------

  // ------ Loop Step Begin ------
  {
    {
      var i: int;
      var buf: int;

      i := 0;
      buf := i0[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 1;
      buf := i1[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }

      i := 2;
      buf := i2[t];
      if buf > 0{
        var pkt := 1;
        bufs.enq(i, pkt);
      }
    }

    {
      var i: int;
      i := 0;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 1;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }

      i := 2;
      if |bufs.bufs[i]| > 0 && !find(nq, i) && !find(oq, i) {
        nq := nq + [i];
      }
    }

    {
      var i: int;
      var dequeued: bool;

      i := 0;
      dequeued := false;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 1;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

      i := 2;
      if !dequeued {
        var head := -1;

        if |nq| > 0{
          head := nq[0];
          nq := nq[1..];
        } else if |oq| > 0 {
          head := oq[0];
          oq := oq[1..];
        }

        if head != -1 {
          if |bufs.bufs[head]| > 1 {
            oq := oq + [head];
          }
          if |bufs.bufs[head]| > 0 {
            bufs.move(head, OUT_BUF_IDX);
            dequeued := true;
          }
        }
      }

    }

    cdeq0 := cdeq0 + [bufs.cdeq[0]];
    t := t + 1;
  }
  // assert cdeq0[t - 1] == 3;
  // ------ Loop Step End ------

  // assert cdeq0[t - 1] >= 3;
  assert query(cdeq0);
  print(cdeq0);
}