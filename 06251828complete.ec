(* ====================================================================
   BIKE — IND-CPA 用スリム統合ファイル
   Bausch の実装から、IND-CPA に必要なファイルのみを1本に統合。

   統合元(依存順): L0(テスト用パラメータ) -> Params -> Utils
                    -> Hashes -> PolyInv -> BIKE(keyGen/encaps)

   除外したもの(理由):
     - BlackGrayFlip.ec / NewBFDecoder.ec : 復号器。IND-CPA に不要(正当性専用)
     - Bike.decaps                         : 復号器を要するため除外

   マージ時に行った修正(元の二重貼り/破損を解消):
     - PolyReduceZp / DynMatrix の clone は Utils 内の1回だけに統一
     - Hashes の重複 clone(ROK) と破損コピー(Algorithm3/H/K)を削除
     - 誤字修正: ZP -> Zp, dunigin -> dunifin, basePoly -> BasePoly,
                 poly_length -> r
     - 複数 ROM clone があるため `LRO` が曖昧。各所を
       `ROK.Lazy.LRO` / `ROL.Lazy.LRO` / `ROSHAKE.Lazy.LRO` / `ROH.Lazy.LRO`
       のように完全修飾(下記 [要確認])
     - プロジェクト内 require import(Params/Utils/Hashes/PolyInv) を削除し
       中身を直接配置。ライブラリ require は先頭に集約
     - 名前修飾 Utils.R -> R, Params.n -> n(同一ファイル内で不要なため)
     - IND-CPA 用に素の PKE 暗号化 BIKE_PKE.enc を追加

   [要確認 — お使いの EC で print/search 検証]
     1. `ROM` 配下のパスが `Lazy.LRO` で正しいか(thesis の import から推定)
     2. `MFinite` を import する理論(下の require に仮置き)
     3. clone 代入 `op n = r` が通るか(ダメなら `<-`)
     4. RFinite/E_tFinite の enum_spec は admitted のまま(健全性は後で要証明)
   ==================================================================== *)
(* パラメータ定義は AllCore+IntDiv だけの状態で先に行う。
   r2025.03 では一部ライブラリがトップレベルで `r` を定義しており、
   重いインポートを先に行うと `op r` が衝突するため(原典 L0.ec と同じ構造)。 *)
require import AllCore IntDiv.

(* ==================================================================== *)
(*  PARAMS  (L0: テスト用。L1/L3/L5 に差し替え可)                        *)
(* ==================================================================== *)
(* System Parameter *)
op r = 37.
op w = 6.
op t = 6.
op l = 256.
(* Decoder Settings (CPA では未使用。faithful 用に残置) *)
op NbIter = 5.
op tau = 3.
op threshold (s i : int) : int = max (floor(0.0069722*s%r+13.530)) 36.
op ft (x : int) = 0.006258 * x%r + 11.094.
op delt = 3.

(* Code length / d = w/2 *)
op n = r + r.
op d = w %/ 2.

lemma w_gt0 : 0 < w. smt. qed.
lemma w_even : 2 %| w. smt. qed.
lemma uneven_w_half : !(2 %| d). smt. qed.
lemma r_gt0 : 0 < r. smt. qed.
lemma r_prime : prime r.
  pose P := (fun q, -r <= q => q %| r => `|q| = 1 \/ `|q| = r).
  have step : forall t, -r <= t => P t => (forall q, q <= t-1 => P q) => forall q, q <= t => P q.
    smt.
  have Hmain : forall q, q <= r => P q.
    rewrite /r.
    do (apply step; [ by trivial | by trivial | simplify ]).
    smt.
  rewrite /prime.
  progress.
  have Hbound : q <= r. smt.
  have Hnegbound : -r <= q.
    have H2 : -r %% -q = 0. rewrite modzN; smt.
    smt.
  apply Hmain; trivial.
qed.

(* パラメータ定義後に、残りのライブラリをインポートする。 *)
require import List Distr IntMin RealExp.
require ROM PolyReduce BitWord DynMatrix.

(* ==================================================================== *)
(*  UTILS  (環/型/変換/分布)                                            *)
(* ==================================================================== *)
clone import PolyReduce.PolyReduceZp as PolyRing
  with op n = r, op p = 2
  proof *.
realize ge2_p. smt. qed.
realize gt0_n. smt. qed.

clone import DynMatrix as Matrix with
  op   ZR.(+) = PolyRing.Zp.(+),
  type ZR.t  <= PolyRing.Zp.

(* Cyclic polynomial ring F_2[X]/(X^r - 1) / message / key spaces *)
type R = polyXnD1.
type M = vector.
type K = vector.

(* From Polynom to Vector *)
op polyToVec (x : polyXnD1) : vector = offunv ((BasePoly.of_poly (prepr x)), r).
(* From Vector to Polynom *)
op vecToPoly (x : vector) : polyXnD1 = polyLX (tolist x).
(* From Vector to Circulant Matrix *)
op vecToCircMatr (x : vector) : matrix =
  offunm ((fun j i : int => x.[(i-j) %% (size x)]), size x, size x).

(* Hamming weight machinery *)
op RListToInt (x : Matrix.R list) =
  with x = []      => []
  with x = y :: ys => Zp.asint y :: RListToInt ys.
op polyToList (x : polyXnD1) = RListToInt (tolist (polyToVec x)).
op ham_weight (x : int list) =
  with x = []      => 0
  with x = y :: ys => ((y=0)?0:1) + (ham_weight ys).
op ham_vector (x : vector) = ham_weight (RListToInt (tolist x)).

(* BIKE <-> Decoder 変換(CPA未使用だが Utils の一部として残置) *)
op toDecoder (s h0 h1 : R) : vector * matrix =
  (polyToVec s, (vecToCircMatr (polyToVec h0)) || (vecToCircMatr (polyToVec h1))).
op fromDecoder (e : vector) : R * R =
  (vecToPoly (subv e 0 (r-1)), vecToPoly (subv e r (n-1))).

(* Counter function *)
op listcount (x y : int list) : int =
  with x = [],      y = []      => 0
  with x = [],      y = w :: ws => 0
  with x = w :: ws, y = []      => 0
  with x = w :: ws, y = v :: vs => ((w=1 && v=1) ? 1 : 0) + listcount ws vs.
op ctr (H : matrix, s : vector, j : int) : int =
  listcount (RListToInt (tolist (col H j))) (RListToInt (tolist s)).

(* bit(vector) -> integer *)
op b2i_recursion (x : int list) (y : int) =
  with x = []      => y
  with x = z :: zs => b2i_recursion zs ((2 * y) + z).
op b2i (x : vector) = b2i_recursion (RListToInt (tolist x)) 0.

(* int list -> polynom *)
op changelist (x : int list, y : int list) =
  with x = []      => y
  with x = z :: zs => changelist zs (put y z 1).
op IntListToR (x : int list) =
  with x = []      => []
  with x = y :: ys => Zp.inzmod y :: IntListToR ys.
op intlistToPoly (x : int list) : R = polyLX (IntListToR (changelist x (nseq r 0))).

(* Polynom exponentiation *)
op ( ^ ) (x : polyXnD1, y : int) = iterop y PolyRing.( * ) x oner.

(* integer -> bit *)
op empty_int_list : int list = [].
op bitSizeComp (x : int) = (x=0) ? 1 : (argmax (fun i => 2^i) (fun j => j<=x)) + 1.
op i2b_iter (x : int * int list) =
  (x.`1 = 0) ? (x.`1, x.`2) : (x.`1 %/ 2, (x.`1 %% 2) :: x.`2).
op i2b (x : int) = oflist (IntListToR (iter (bitSizeComp x) i2b_iter (x, empty_int_list)).`2).

(* uniform over M = {0,1}^l *)
op duniformM = Matrix.Vectors.dvector Zp.DZmodP.dunifin l.

(* uniform over E_t (R * R) with |e0|+|e1| = t *)
op filter_Et (x : (R * R)) : bool =
  (ham_weight (polyToList x.`1) + ham_weight (polyToList x.`2) = t).
op list_append_each ['a 'b] (s : 'a list) (t : 'b) =
  with s = []      => []
  with s = x :: xs => (t, x) :: list_append_each xs t.
op double_list (s : 'a list) (t : 'b list) =
  with s = []      => []
  with s = x :: xs => list_append_each t x ++ double_list xs t.
op enumR : R list = map polyLX (alltuples r Zp.DZmodP.Support.enum).
op enumE_t = filter filter_Et (double_list enumR enumR).

(* ★要証明・数学的に真：enumR が R 全体を網羅列挙（一様性の台被覆）。
   構成証明が重いため公理として明示。困難性仮定とは別の良性公理。 *)
axiom enumR_spec : forall (x : R), count (pred1 x) enumR = 1.

clone MFinite as RFinite with type t <- R, op Support.enum <- enumR proof *.

realize Support.enum_spec. exact enumR_spec. qed.
  
op distribution_over_R = RFinite.dunifin.

op distribution_over_E_t : (R * R) distr = duniform enumE_t.

(* ==================================================================== *)
(*  HASHES  (K, L, SHAKE, H, H2 を ROM で)                              *)
(* ==================================================================== *)
require ROM.   (* 既に上で require 済みだが faithful 用 *)

(* hash function K : M * R * M -> K *)
clone ROM as ROK with
  type in_t   <- M * R * M,
  type out_t  <- K,
  op   dout _ <- dvector Zp.DZmodP.dunifin l.
module K = {
  proc init(): unit = { ROK.Lazy.LRO.init(); }
  proc hash(x : M * R * M): K = { var y; y <@ ROK.Lazy.LRO.o(x); return y; }
}.

(* hash function L : R * R -> M *)
clone ROM as ROL with
  type in_t   <- R * R,
  type out_t  <- M,
  op   dout _ <- dvector Zp.DZmodP.dunifin l
  proof *.
module L = {
  proc init(): unit = { ROL.Lazy.LRO.init(); }
  proc hash(x : R * R): M = { var y; y <@ ROL.Lazy.LRO.o(x); return y; }
}.

(* SHAKE256 stream oracle *)
clone ROM as ROSHAKE with
  type in_t   <- vector * int,
  type out_t  <- vector,
  op   dout _ <- dvector Zp.DZmodP.dunifin 32
  proof *.
module SingleStream = {
  proc init(): unit = { ROSHAKE.Lazy.LRO.init(); }
  proc hash(x : vector * int): M = { var y; y <@ ROSHAKE.Lazy.LRO.o(x); return y; }
}.

(* WSHAKE256-PRF (Algorithm 3) — 正しい版(両 while を持つ) *)
module Algorithm3 = {
  proc main(seed : vector, len : int, wt : int): int list = {
    var j <- 0;
    var tmp;
    var i <- wt-1;
    var pos : int;
    var wlist : int list <- [];
    var s : vector list <- [];
    while (j < wt) {
      tmp <@ SingleStream.hash(seed, j);
      s <- rcons s tmp;
      j <- j + 1;
    }
    while (0 < (i+1)) {
      pos <- i + floor((len - i)%r * (b2i (nth (zerov 0) s i))%r / (2^32)%r);
      if (mem wlist pos) { wlist <- rcons wlist i; }
      else { wlist <- rcons wlist pos; }
      i <- i - 1;
    }
    return wlist;
  }
}.

(* hash function H : M -> E_t (Algorithm3 経由) *)
module H = {
  proc hash(x) = {
    var tmp, h0, h1;
    tmp <@ Algorithm3.main(x, 2*r, t);
    h0 <- intlistToPoly (take r tmp);
    h1 <- intlistToPoly (drop r tmp);
    return (h0, h1);
  }
}.

(* H の単純版(ROM) *)
clone ROM as ROH with
  type in_t   <- M,
  type out_t  <- (R * R),
  op   dout _ <- distribution_over_E_t.
module H2 = {
  proc init(): unit = { ROH.Lazy.LRO.init(); }
  proc hash(x : M): (R * R) = { var y; y <@ ROH.Lazy.LRO.o(x); return y; }
}.

(* ==================================================================== *)
(*  POLYINV  (Algorithm 2)                                              *)
(* ==================================================================== *)
module Algorithm2 = {
  proc invert(a : R) : R = {
    var i <- 1;
    var g : R;
    var f <- a;
    var result <- a;
    while (i < floor(ln (r-2)%r)+1) {
      g <- f ^ (2 ^ (2 ^ (i-1)));
      f <- f * g;
      if (Zp.asint (Matrix.Vectors.get (i2b (r-2)) i) = 1) {
        result <- result * f ^ (2 ^ ((r-2) %% 2^i));
      }
      result <- result * result;
      i <- i + 1;
    }
    return result;
  }
}.

(* ==================================================================== *)
(*  BIKE  (KEM: keyGen, encaps。decaps は除外)                          *)
(* ==================================================================== *)
module Bike = {
  proc keyGen(): (R * R) * M * R = {
    var tmp;
    var h0, h1 : polyXnD1;
    var sk : (polyXnD1 * polyXnD1);
    var pk;
    var seed0, seed1 : M;
    var sigma : M;
    seed0 <$ duniformM;
    tmp <@ Algorithm3.main(seed0, r, floor (w%r/2%r));
    h0  <- intlistToPoly tmp;
    seed1 <$ duniformM;
    tmp <@ Algorithm3.main(seed1, r, floor (w%r/2%r));
    h1  <- intlistToPoly tmp;
    sk  <- (h0, h1);
    h0  <@ Algorithm2.invert(sk.`1);
    pk  <- (h1 * h0);
    sigma <$ duniformM;
    return (sk, sigma, pk);
  }

  proc encaps(pk : R): K * (R * M) = {
    var m : M;
    var e0, e1 : R;
    var c : R * M;
    var k : K;
    var e_hashed : M;
    m <$ duniformM;
    (e0, e1) <@ H.hash(m);
    e_hashed <@ L.hash(e0, e1);
    c <- (e0 + e1*pk, m + e_hashed);
    k <@ K.hash(m, c.`1, c.`2);
    return (k, c);
  }
}.

(* (旧 BIKE_PKE モジュールは削除。KEM 版 IND-CPA 証明では keyGen/encaps を
    使うため不要。PKE レベルの enc が必要になったら別途復活させる。) *)

(* ==================================================================== *)
(*  IND-CPA (KEM 鍵擬似ランダム性) : Game0..Game5 と帰着スケルトン        *)
(*  目標: |Pr[Game0]-Pr[Game5]| <= 2*eps_qccf + 2*eps_qcsd + (ROM 項)     *)
(*  ※ 証明は admit。各ホップに「真似すべき HQC 補題」とレシピを付した。   *)
(* ==================================================================== *)
op duniformK = duniformM.   (* uniform over K (= M と同型) *)

  (* oracle interface *)
module type OrclH = { proc hash(_ : M) : R * R}.
module type OrclL = { proc hash(_ : R * R) : M }.
module type OrclK = { proc hash(_ : M * R * M) : K }.

module type Adv (OH : OrclH) (OL : OrclL) (OK : OrclK) = {
  proc guess(pk : R, c : R * M, k : K) : bool {OH.hash, OL.hash, OK.hash}
  }.

(* 仮定1: (2,1)-QC Codeword Finding  (公開鍵 h の擬似ランダム性, Def 14) *)
module type CF_Dist = { proc distinguish(h : R) : bool }.
module DQCCF (D : CF_Dist) = {
  proc main(b : bool) : bool = {
    var sk, sigma, hk, hu, h, r0;
    (sk, sigma, hk) <@ Bike.keyGen();    (* hk = h1*h0^{-1} (構造化) *)
    hu <$ distribution_over_R;            (* 一様 *)
    h  <- if b then hu else hk;
    r0 <@ D.distinguish(h);
    return r0;
  }
}.

(* 仮定2: (2,1)-QC Syndrome Decoding  (シンドローム c0 の擬似ランダム性, Def 13)
   ※ ここで h は一様(Game1 以降の世界に合わせる)。 *)
module type SD_Dist = { proc distinguish(h : R, s : R) : bool }.
module DQCSD (D : SD_Dist) = {
  proc main(b : bool) : bool = {
    var h, e0, e1, ss, su, s, r0;
    h <$ distribution_over_R;
    (e0, e1) <$ distribution_over_E_t;
    ss <- e0 + e1 * h;
    su <$ distribution_over_R;
    s  <- if b then su else ss;
    r0 <@ D.distinguish(h, s);
    return r0;
  }
}.

op eps_qccf : real.
op eps_qcsd : real.
op eps_rom  : real.   (* ROM bad-event(L/K)の上界の総称。後で qK*2^-l 等に具体化 *)

(* ===== ルートA: ROM guessing bound 用の追加（量的土台） ===== *)
(* A のクエリ上界（後段の counting で cnt <= qH/qK を確立する用） *)
op qH : int.
op qK : int.
(* eps_rom を ROM guessing bound の上界として配線（主定理は不変） *)
axiom eps_rom_qH : qH%r / (2^l)%r <= eps_rom.
axiom eps_rom_qK : qK%r / (2^l)%r <= eps_rom.
axiom eps_rom_qHK : (qH + qK)%r / (2^l)%r <= eps_rom.
axiom qH_ge0 : 0 <= qH.
axiom qK_ge0 : 0 <= qK.

(* card = 2（p=2 のクローン） *)
lemma card2 : Zp.DZmodP.Support.card = 2.
proof. by rewrite Zp.DZmodP.cardE. qed.

(* 成分一様分布の点質量 = 1/2 *)
lemma mu1_dunifin_half : mu1 Zp.DZmodP.dunifin witness = 1%r / 2%r.
    proof. by rewrite Zp.DZmodP.dunifin1E card2. qed.

(* メッセージ空間 M=duniformM の点質量は 2^-l で上から抑えられる *)
lemma mu1_duniformM_le (x : M) : mu1 duniformM x <= 1%r / (2^l)%r.
proof.
  rewrite /duniformM.
  case (size x = l) => hsz; last first.
  - rewrite get_dvector0E.
    + by rewrite /max /=; smt().
    have h2l : 0 < 2^l by smt(StdOrder.IntOrder.expr_gt0).
    smt().
  - rewrite -hsz mu1_dvector_fu; first exact Zp.DZmodP.dunifin_funi.
    rewrite mu1_dunifin_half hsz.
    have -> : 1%r / 2%r = inv 2%r by smt().
    rewrite RField.exprVn 1:/#.
    rewrite RField.fromintXn 1:/#.
    smt().
qed.

op negl = (size enumE_t)%r / RFinite.Support.card%r.

lemma mem_list_append_each ['a 'b] (a : 'a) (b : 'b) (x : 'a) (t : 'b list) :
  (a, b) \in list_append_each t x <=> a = x /\ b \in t.
proof. elim: t => /=; smt(). qed.

lemma mem_double_list ['a 'b] (a : 'a) (b : 'b) (s : 'a list) (t : 'b list) :
  (a, b) \in double_list s t <=> a \in s /\ b \in t.
proof.
  elim: s => /= [|x xs ih]; first by rewrite /double_list.
  rewrite mem_cat mem_list_append_each ih; smt().
qed.

lemma mem_enumR (a : R) : a \in enumR.
    proof.
      have := RFinite.Support.enum_spec a; smt(count_ge0 has_count hasP).
  qed.

lemma Et_complete (x : R * R) : filter_Et x => x \in enumE_t.
proof.
  move=> hx; rewrite /enumE_t mem_filter hx /=.
  have -> : x = (x.`1, x.`2) by smt().
  rewrite mem_double_list; smt(mem_enumR).
qed.

lemma fp_measure (h : R) :
  mu distribution_over_R
     (fun (su : R) => su \in map (fun (x : R * R) => x.`1 + x.`2 * h) enumE_t) <= negl.
proof.
  rewrite /negl.
  have hb : forall (x : R), mu1 distribution_over_R x <= 1%r / RFinite.Support.card%r.
  + move=> x; rewrite /distribution_over_R RFinite.dunifin1E; smt().
  have h1 := mu_mem_le_mu1 distribution_over_R
               (map (fun (x : R * R) => x.`1 + x.`2 * h) enumE_t)
               (1%r / RFinite.Support.card%r) hb.
  rewrite size_map in h1.
  have hmem :
    (fun (su : R) => su \in map (fun (x : R * R) => x.`1 + x.`2 * h) enumE_t)
      = mem (map (fun (x : R * R) => x.`1 + x.`2 * h) enumE_t)
    by apply fun_ext => su.
  rewrite hmem; smt().
qed.

  (* QCCF reduction *)
module Red_cf (A : Adv) : CF_Dist = {
  proc distinguish(h : R) : bool = {
  var m, e0, e1, eh, c, k, b';
  H2.init(); L.init(); K.init();
  m <$ duniformM;
    (e0, e1) <@  H2.hash(m);
      eh <@ L.hash(e0, e1);
      c <- (e0 + e1 * h, m + eh);
      k <@ K.hash(m, c.`1, c.`2);
      b' <@ A(H2, L, K).guess(h, c, k);
      return b';
  }
}.

module Red_cf_rand (A : Adv) : CF_Dist = {
  proc distinguish(h : R) : bool = {
  var m, e0, e1, eh, c, k, b';
  H2.init(); L.init(); K.init();
  m <$ duniformM;
    (e0, e1) <@H2.hash(m);
      eh <@ L.hash(e0, e1);
      c <- (e0 + e1 * h, m +eh);
      k <$ duniformK;
      b' <@ A(H2, L, K).guess(h, c, k);
      return b';
  }
}.

module Red_sd_bad (A : Adv) : SD_Dist = {
  var found : bool
  var hh : R
  var ss : R

  module OL : OrclL = {
    proc hash(x : R * R) : M = {
    var y;
    if(x.`1 + x.`2 * Red_sd_bad.hh = Red_sd_bad.ss /\ filter_Et x) {
    Red_sd_bad.found <- true;
      }
          y <@ L.hash(x);
      return y;
    }
  }

      proc distinguish(h : R, s : R) : bool = {
      var m, lmask, c, k, b';
      H2.init(); L.init(); K.init();
      Red_sd_bad.found <- false; Red_sd_bad.hh <- h; Red_sd_bad.ss <- s;
      m <$ duniformM; lmask <$ duniformM;
      c <- (s, m + lmask);
      k <@ K.hash(m, c.`1, c.`2);
      b' <@ A(H2, OL, K).guess(h, c, k);
      return Red_sd_bad.found;
  }
}.

module Red_sd_rand_bad (A : Adv) : SD_Dist = {
  var found : bool
  var hh : R
  var ss : R
  module OL : OrclL = {
    proc hash(x : R * R) : M = {
    var y;
    if (x.`1 + x.`2 * Red_sd_rand_bad.hh = Red_sd_rand_bad.ss /\ filter_Et x) {
    Red_sd_rand_bad.found <- true;
      }
          y <@ L.hash(x);
          return y;
    }
  }

      proc distinguish(h : R, s : R): bool = {
      var m, lmask, c, k, b';
      H2.init(); L.init(); K.init();
      Red_sd_rand_bad.found <- false;
      Red_sd_rand_bad.hh <- h; Red_sd_rand_bad.ss <- s;
      m <$ duniformM; lmask <$ duniformM;
      c <- (s, m + lmask);
      k <$ duniformK;
      b' <@ A(H2, OL, K).guess(h, c, k);
      return Red_sd_rand_bad.found;
  }
}.

(* bad flag for G2<=>G3 *)
module BadK : OrclK = {
  var bad : bool
  var secret : M * R * M
  proc hash(x : M * R * M) : K = {
  var y;
    if (x = BadK.secret) { BadK.bad <- true; }
  y <@ K.hash(x);
  return y;
  }
}.

module BadL : OrclL = {
  var bad : bool
  var secret : R * R
  proc hash(x : R * R) : M = {
  var y;
    if (x = BadL.secret) { BadL.bad <- true; }
  y <@ L.hash(x);
  return y;
  }
}.

module BadH : OrclH = {
  var bad : bool
  var secret : M
  proc hash(x : M) : R * R = {
  var y;
    if (x = BadH.secret) { BadH.bad <- true; }
  y <@H2.hash(x);
  return y;
  }
}.

module BadHc : OrclH = {
  var bad : bool
  var secret : M
  var cnt : int
  var qs : M list
  proc hash(x : M) : R * R = {
    var y;
    if (x = BadHc.secret) { BadHc.bad <- true; }
    BadHc.cnt <- BadHc.cnt + 1;
    BadHc.qs <- rcons BadHc.qs x;
    y <@ H2.hash(x);
    return y;
  }
}.

module BadKc : OrclK = {
  var bad : bool
  var secret : M * R * M
  var cnt : int
  var qs : (M * R * M) list
  proc hash(x : M * R * M) : K = {
    var y;
    if (x = BadKc.secret) { BadKc.bad <- true; }
    BadKc.cnt <- BadKc.cnt + 1;
    BadKc.qs <- rcons BadKc.qs x;
    y <@ K.hash(x);
    return y;
  }
}.

lemma duniformM_ll : is_lossless duniformM.
    proof.
      rewrite /duniformM;
      apply dvector_ll;
      exact Zp.DZmodP.dunifin_ll.
  qed.

lemma DR_ll : is_lossless distribution_over_R.
    proof.
      rewrite /distribution_over_R;
      exact RFinite.dunifin_ll.
  qed.

(* ★要証明・数学的に真：重み和 = t の誤りベクトル対が存在（E_t 非空）。
   polyToList/ham_weight 経由の構成証明が重いため公理として明示。
   除去済みの偽公理 E_tFinite.enum_spec とは異なり、これは真の事実。 *)
axiom exists_filter_Et : exists (x : R * R), filter_Et x.

lemma enumE_t_nonempty : enumE_t <> [].
proof.
  have [e he] := exists_filter_Et.
  have hmem := Et_complete e he.
  apply/negP => h.
  by move: hmem; rewrite h.
qed.

lemma DEt_ll : is_lossless distribution_over_E_t.
proof.
  rewrite /distribution_over_E_t.
  apply duniform_ll.
  exact enumE_t_nonempty.
qed.

  lemma dvec32_ll : weight (dvector Zp.DZmodP.dunifin 32) = 1%r.
proof. apply dvector_ll; exact Zp.DZmodP.dunifin_ll. qed.

lemma sstream_ll : islossless SingleStream.hash.
    proof.
      proc.
      inline ROSHAKE.Lazy.LRO.o.
    auto => />.
    smt(dvec32_ll).
  qed.

lemma alg3_ll : islossless Algorithm3.main.
    proof.
      proc.
      while (true) (i + 1); first by move => z;  auto; smt().
      wp; while (true) (wt - j); first by move => z; wp; call sstream_ll; auto; smt().
      by auto; smt().
  qed.

lemma alg2_ll : islossless Algorithm2.invert.
    proof.
      proc; while(true) (floor (ln (r - 2)%r) + 1 - i); first by auto; smt().
      by auto; smt.
  qed.

lemma keyGen_ll : islossless Bike.keyGen.
    proof.
      proc.
      rnd; wp; call alg2_ll; wp;
      call alg3_ll; rnd; wp;
      call alg3_ll; rnd.
      by auto; smt(duniformM_ll).
  qed.

lemma keyGen_eq :
equiv[Bike.keyGen ~ Bike.keyGen :
      ={glob ROSHAKE.Lazy.LRO} ==> ={res, glob ROSHAKE.Lazy.LRO}].
    proof. proc; sim. qed.

lemma K_hash_ll : islossless K.hash.
    proof. proc; inline ROK.Lazy.LRO.o; auto => />; smt(duniformM_ll). qed.

lemma L_hash_ll : islossless L.hash.
    proof. proc; inline ROL.Lazy.LRO.o; auto => />; smt(duniformM_ll). qed.

lemma H2_hash_ll : islossless H2.hash.
    proof. proc; inline ROH.Lazy.LRO.o; auto => />; smt(DEt_ll). qed.

lemma BadK_hash_ll : islossless BadK.hash.
    proof. proc; call K_hash_ll; auto. qed.

lemma duniformK_dvec : duniformK = dvector Zp.DZmodP.dunifin l.
    proof. by rewrite /duniformK /duniformM. qed.

lemma BadL_hash_ll : islossless BadL.hash.
    proof. proc; call L_hash_ll; auto. qed.

lemma BadH_hash_ll : islossless BadH.hash.
    proof. proc; call H2_hash_ll; auto. qed.

lemma BadHc_hash_ll : islossless BadHc.hash.
    proof. proc; call H2_hash_ll; auto. qed.
    
lemma H2_hash_eq :
equiv[H2.hash ~ H2.hash : = {arg, ROH.Lazy.LRO.m} ==> ={res, ROH.Lazy.LRO.m}].
    proof. proc; inline ROH.Lazy.LRO.o; auto => />. qed.

lemma L_hash_eq :
equiv[L.hash ~ L.hash : ={arg, ROL.Lazy.LRO.m} ==> ={res, ROL.Lazy.LRO.m}].
    proof. proc; inline ROL.Lazy.LRO.o; auto => />. qed.

lemma K_hash_eq :
equiv[K.hash ~ K.hash : ={arg, ROK.Lazy.LRO.m} ==> ={res, ROK.Lazy.LRO.m}].
    proof. proc; inline ROK.Lazy.LRO.o; auto => />. qed.

  (* duniformM の台では size = l。その上で平行移動が全単射＆点質量保存 *)
lemma duniformM_size (v : M) : v \in duniformM => size v = l.
proof.
  rewrite /duniformM => hv; have := size_dvector Zp.DZmodP.dunifin l v hv.
  smt().   (* max 0 l = l （l=256>0） *)
qed.

lemma vec_subrK (m v : M) : size m = l => size v = l => m + (v - m) = v.
proof.
  move=> hm hv.
  have e1 : v - m = -m + v by apply Vectors.addvC.
  rewrite e1 Vectors.addvA.
  have e2 : m + -m = zerov l.
  + have := Vectors.addvN m.            (* m - m = zerov (size m) *)
    rewrite hm => ->; reflexivity.
  rewrite e2.
  have := Vectors.add0v v.              (* zerov (size v) + v = v *)
  rewrite hv => ->; reflexivity.
qed.

lemma vec_subrK2 (m v : M) : size m = l => size v = l => m + v - m = v.
proof.
  move=> hm hv.
  rewrite (Vectors.addvC m v) -Vectors.addvA.
  have e2 : m + -m = zerov l.
  + have h := Vectors.addvN m. rewrite hm in h. exact h.
  rewrite e2.
  have hlv : l = size v by rewrite hv.
  by rewrite (Vectors.lin_addv0 v l hlv).
qed.

lemma duniformM_funi (v1 v2 : M) :
  size v1 = l => size v2 = l => mu1 duniformM v1 = mu1 duniformM v2.
proof.
  move=> h1 h2; rewrite /duniformM.
  rewrite -{1}h1 -{1}h2 !mu1_dvector_fu; first exact Zp.DZmodP.dunifin_funi.
  + exact Zp.DZmodP.dunifin_funi.
  by rewrite h1 h2.
qed.

lemma vec_subv_supp (m v : M) :
  size m = l => v \in duniformM => (v - m) \in duniformM.
proof.
  move=> hm hv.
  have hsz : size v = l by apply duniformM_size.
  have hl : 0 <= l by smt().
  rewrite /duniformM (supp_dvector Zp.DZmodP.dunifin (v - m) l hl).
  rewrite size_addv size_oppv hsz hm /=.
  split; first smt().
  move=> i hi.
  rewrite get_addv getvN.
  exact Zp.DZmodP.dunifin_fu.
qed.

section Security.
  declare module A <: Adv {-Bike, -K, -L, -H2, -Algorithm2, -Algorithm3, -ROK.Lazy.LRO, -ROL.Lazy.LRO, -ROSHAKE.Lazy.LRO, -ROH.Lazy.LRO, -BadK, -BadL, -BadH, -BadHc, -BadKc, -Red_sd_bad, -Red_sd_rand_bad}.

  declare axiom qccf_hard &m (D <: CF_Dist) :
    `| Pr[DQCCF(D).main(false) @ &m : res] - Pr[DQCCF(D).main(true) @ &m : res] | <= eps_qccf.
  declare axiom qcsd_hard &m (D <: SD_Dist) :
    `| Pr[DQCSD(D).main(false) @ &m : res] - Pr[DQCSD(D).main(true) @ &m : res] | <= eps_qcsd.

  declare axiom A_guess_ll (OH <: OrclH{-A}) (OL <: OrclL{-A}) (OK <: OrclK{-A}) :
    islossless OH.hash => islossless OL.hash => islossless OK.hash =>
    islossless A(OH, OL, OK).guess.

  (* A は H オラクル(第1引数)を高々 qH 回しか引かない。
     BadHc.cnt は H クエリ回数を数えるので、guess 実行後に cnt <= qH。 *)
  declare axiom A_qH_bound :
    hoare[ A(BadHc, L, K).guess :
    BadHc.qs = [] ==> size BadHc.qs <= qH ].

  declare axiom A_qK_bound :
  hoare[ A(H2, L, BadKc).guess :
         BadKc.qs = [] ==> size BadKc.qs <= qK ].

  (* Game0: 全て本物(実 pk, 実 c, 実 K) *)
  module Game0 = { proc main() : bool = {
    var sk, sigma, pk, m, e0, e1, eh, c, k, b';
    H2.init(); L.init(); K.init();
    (sk, sigma, pk) <@ Bike.keyGen();
    m <$ duniformM;
    (e0, e1) <@ H2.hash(m);
    eh <@ L.hash(e0, e1);
    c <- (e0 + e1 * pk, m + eh);
    k <@ K.hash(m, c.`1, c.`2);
    b' <@ A(H2, L, K).guess(pk, c, k);
    return b';
  } }.

      (* Game1: pk を一様化  [G0<->G1 : QCCF, クリーン] *)
  module Game1 = { proc main() : bool = {
    var pk, m, e0, e1, eh, c, k, b';
    H2.init(); L.init(); K.init();
    pk <$ distribution_over_R;
    m <$ duniformM;
    (e0, e1) <@ H2.hash(m);
    eh <@ L.hash(e0, e1);
    c <- (e0 + e1 * pk, m + eh);
    k <@ K.hash(m, c.`1, c.`2);
    b' <@ A(H2, L, K).guess(pk, c, k);
    return b';
  } }.

module Game1_bad = { proc main() : bool = {
  var pk, m, e0, e1, eh, c, k, b';
  H2.init(); L.init(); K.init();
  pk <$ distribution_over_R;
  m <$ duniformM;
    (e0, e1) <@ H2.hash(m);
      eh <@ L.hash(e0, e1);
      c <- (e0 + e1 * pk, m + eh);
      k <@ K.hash(m, c.`1, c.`2);
      BadL.bad <- false; BadL.secret <- (e0, e1);
      BadH.bad <- false; BadH.secret <- m;
      b' <@ A(BadH, BadL, K).guess(pk, c, k);
      return b';
  }}.

(* Game2: remove c1 from L *)
module Game2 = { proc main() : bool = {
  var pk, m, e0, e1, lmask, c, k, b';
  H2.init(); L.init(); K.init();
  pk <$ distribution_over_R;
  m <$ duniformM;
    (e0, e1) <$ distribution_over_E_t;
      lmask <$ duniformM;
      c <- (e0 + e1 * pk, m + lmask);
      k <@ K.hash(m, c.`1, c.`2);
      b' <@ A(H2, L, K).guess(pk, c, k);
      return b';
  }}.

module Game2_bad = { proc main() : bool = {
  var pk, m, e0, e1, lmask, c, k, b';
  H2.init(); L.init(); K.init();
  pk <$ distribution_over_R;
  m <$ duniformM;
    (e0, e1) <$ distribution_over_E_t;
      lmask <$ duniformM;
      c <- (e0 + e1 * pk, m + lmask);
      k <@ K.hash(m, c.`1, c.`2);
      BadL.bad <- false; BadL.secret <- (e0, e1);
      BadH.bad <- false; BadH.secret <- m;
      b' <@ A(BadH, BadL, K).guess(pk, c, k);
      return b';
  }}.

module Game2_bK = { proc main() : bool = {
  var pk, m, e0, e1, lmask, c, k, b';
  H2.init(); L.init(); K.init();
  pk <$ distribution_over_R;
  m <$duniformM;
    (e0, e1) <$ distribution_over_E_t;
      lmask <$duniformM;
      c <- (e0 + e1 * pk, m + lmask);
      k <@ K.hash(m, c.`1, c.`2);
      BadK.bad <- false; BadK.secret <- (m, c.`1, c.`2);
      b' <@ A(H2, L, BadK).guess(pk, c, k);
      return b';
  }}.

        (* Game3: c0 construction *)
  module Game3 = { proc main() : bool = {
    var pk, m, e0, e1, lmask, c, k, b';
    H2.init(); L.init(); K.init();
    pk <$ distribution_over_R;
    m <$ duniformM;
      (e0, e1) <$ distribution_over_E_t;
        lmask <$ duniformM;
        c <- (e0 + e1 * pk, m + lmask);
        k <$ duniformK;
        b' <@ A(H2, L, K).guess(pk, c, k);
        return b';
    }}.

  module Game3_bad = { proc main() : bool = {
    var pk, m, e0, e1, lmask, c, k, b';
    H2.init(); L.init(); K.init();
    pk <$ distribution_over_R;
    m <$ duniformM;
    (e0, e1) <$ distribution_over_E_t;
    lmask <$ duniformM;
    c <- (e0 + e1 * pk, m + lmask);
    k <$ duniformK;
    BadL.bad <- false; BadL.secret <- (e0, e1);
    BadH.bad <- false; BadH.secret <- m;
    b' <@ A(BadH, BadL, K).guess(pk, c, k);
    return b';
  }}.

module Game3_bad_c = { proc main() : bool = {
    var pk, m, e0, e1, lmask, c, k, b';
    H2.init(); L.init(); K.init();
    pk <$ distribution_over_R;
    m <$ duniformM;
    (e0, e1) <$ distribution_over_E_t;
    lmask <$ duniformM;
    c <- (e0 + e1 * pk, m + lmask);
    k <$ duniformK;
    BadHc.bad <- false; BadHc.secret <- m; BadHc.cnt <- 0; BadHc.qs <- [];
    b' <@ A(BadHc, L, K).guess(pk, c, k);
    return b';
  }}.

(* m を A 後段へ送り、bad を m∈qs で判定する中継ゲーム。
     BadHc は secret 比較を「しない」運用にしたいが、既存 BadHc を使い回すため
     secret には A の視界と無関係なダミー(witness)を入れ、qs だけ使う。 *)
  module Game3_bad_q = { proc main() : bool = {
    var pk, m, e0, e1, c1, c, k, b';
    H2.init(); L.init(); K.init();
    pk <$ distribution_over_R;
    (e0, e1) <$ distribution_over_E_t;
    c1 <$ duniformM;                 (* OTP: m+lmask を一様 c1 に置換済み *)
    c <- (e0 + e1 * pk, c1);
    k <$ duniformK;
    BadHc.bad <- false; BadHc.secret <- witness; BadHc.cnt <- 0; BadHc.qs <- [];
    b' <@ A(BadHc, L, K).guess(pk, c, k);
    m <$ duniformM;                  (* m を後段でサンプル *)
    return (m \in BadHc.qs);
  }}.

(* 第1段の到達点: OTP 済みだが m は secret に残る *)
  module Game3_bad_c1 = { proc main() : bool = {
    var pk, m, e0, e1, c1, c, k, b';
    H2.init(); L.init(); K.init();
    pk <$ distribution_over_R;
    m <$ duniformM;
    (e0, e1) <$ distribution_over_E_t;
    c1 <$ duniformM;
    c <- (e0 + e1 * pk, c1);
    k <$ duniformK;
    BadHc.bad <- false; BadHc.secret <- m; BadHc.cnt <- 0; BadHc.qs <- [];
    b' <@ A(BadHc, L, K).guess(pk, c, k);
    return BadHc.bad;
  }}.

module Game3_bad_c1e = { proc main() : bool = {
  var pk, m, e0, e1, c1, c, k, b';
  H2.init(); L.init(); K.init();
  pk <$ distribution_over_R;
  m <$ duniformM;
  (e0, e1) <$ distribution_over_E_t;
  c1 <$ duniformM;
  c <- (e0 + e1 * pk, c1);
  k <$ duniformK;
  BadHc.bad <- false; BadHc.secret <- witness; BadHc.cnt <- 0; BadHc.qs <- [];
  b' <@ A(BadHc, L, K).guess(pk, c, k);
  return (m \in BadHc.qs);
}}.

  module Game3_bK = { proc main() : bool = {
    var pk, m, e0, e1, lmask, c, k, b';
    H2.init(); L.init(); K.init();
    pk <$ distribution_over_R;
    m <$ duniformM;
      (e0, e1) <$ distribution_over_E_t;
        lmask <$ duniformM;
        c <- (e0 + e1 * pk, m + lmask);
        k <$ duniformK;
        BadK.bad <- false; BadK.secret <- (m, c.`1, c.`2);
        b' <@ A(H2, L, BadK).guess(pk, c, k);
        return b';
    }}.

  module Game3_bK_c = { proc main() : bool = {
  var pk, m, e0, e1, lmask, c, k, b';
  H2.init(); L.init(); K.init();
  pk <$ distribution_over_R;
  m <$ duniformM;
  (e0, e1) <$ distribution_over_E_t;
  lmask <$ duniformM;
  c <- (e0 + e1 * pk, m + lmask);
  k <$ duniformK;
  BadKc.bad <- false; BadKc.secret <- (m, c.`1, c.`2); BadKc.cnt <- 0; BadKc.qs <- [];
  b' <@ A(H2, L, BadKc).guess(pk, c, k);
  return BadKc.bad;
}}.

module Game3_bK_c1 = { proc main() : bool = {
  var pk, m, e0, e1, c1, c, k, b';
  H2.init(); L.init(); K.init();
  pk <$ distribution_over_R;
  m <$ duniformM;
  (e0, e1) <$ distribution_over_E_t;
  c1 <$ duniformM;
  c <- (e0 + e1 * pk, c1);
  k <$ duniformK;
  BadKc.bad <- false; BadKc.secret <- (m, c.`1, c.`2); BadKc.cnt <- 0; BadKc.qs <- [];
  b' <@ A(H2, L, BadKc).guess(pk, c, k);
  return BadKc.bad;
}}.

module Game3_bK_c1e = { proc main() : bool = {
  var pk, m, e0, e1, c1, c, k, b';
  H2.init(); L.init(); K.init();
  pk <$ distribution_over_R;
  m <$ duniformM;
  (e0, e1) <$ distribution_over_E_t;
  c1 <$ duniformM;
  c <- (e0 + e1 * pk, c1);
  k <$ duniformK;
  BadKc.bad <- false; BadKc.secret <- witness; BadKc.cnt <- 0; BadKc.qs <- [];
  b' <@ A(H2, L, BadKc).guess(pk, c, k);
  return (m \in map (fun (x : M * R * M) => x.`1) BadKc.qs);
}}.

module Game3_bK_q = { proc main() : bool = {
  var pk, m, e0, e1, c1, c, k, b';
  H2.init(); L.init(); K.init();
  pk <$ distribution_over_R;
  (e0, e1) <$ distribution_over_E_t;
  c1 <$ duniformM;
  c <- (e0 + e1 * pk, c1);
  k <$ duniformK;
  BadKc.bad <- false; BadKc.secret <- witness; BadKc.cnt <- 0; BadKc.qs <- [];
  b' <@ A(H2, L, BadKc).guess(pk, c, k);
  m <$ duniformM;
  return (m \in map (fun (x : M * R * M) => x.`1) BadKc.qs);
}}.

module Game2_bad_bK = { proc main() : bool = {
  var pk, m, e0, e1, lmask, c, k, b';
  H2.init(); L.init(); K.init();
  pk <$ distribution_over_R;
  m <$ duniformM;
  (e0, e1) <$ distribution_over_E_t;
  lmask <$ duniformM;
  c <- (e0 + e1 * pk, m + lmask);
  k <@ K.hash(m, c.`1, c.`2);
  BadH.bad <- false; BadH.secret <- m;
  BadK.bad <- false; BadK.secret <- (m, c.`1, c.`2);
  b' <@ A(BadH, L, BadK).guess(pk, c, k);
  return BadH.bad;
}}.

module Game3_bad_bK = { proc main() : bool = {
  var pk, m, e0, e1, lmask, c, k, b';
  H2.init(); L.init(); K.init();
  pk <$ distribution_over_R;
  m <$ duniformM;
  (e0, e1) <$ distribution_over_E_t;
  lmask <$ duniformM;
  c <- (e0 + e1 * pk, m + lmask);
  k <$ duniformK;
  BadH.bad <- false; BadH.secret <- m;
  BadK.bad <- false; BadK.secret <- (m, c.`1, c.`2);
  b' <@ A(BadH, L, BadK).guess(pk, c, k);
  return BadH.bad;
}}.

  (* Game4: c0 を構造化へ戻す  [G3<->G4 : QCSD 逆 + ROM 逆] *)
  module Game4 = { proc main() : bool = {
    var pk, m, e0, e1, eh, c, k, b';
    H2.init(); L.init(); K.init();
    pk <$ distribution_over_R;
    m <$ duniformM;
    (e0, e1) <@ H2.hash(m);
    eh <@ L.hash(e0, e1);
    c <- (e0 + e1 * pk, m + eh);
    k <$ duniformK;
    b' <@ A(H2, L, K).guess(pk, c, k);
    return b';
  } }.

module Game4_bad = { proc main() : bool = {
  var pk, m, e0, e1, eh, c, k, b';
  H2.init(); L.init(); K.init();
  pk <$ distribution_over_R;
  m <$ duniformM;
    (e0, e1) <@ H2.hash(m);
      eh <@ L.hash(e0, e1);
      c <- (e0 + e1 * pk, m + eh);
      k <$ duniformK;
      BadL.bad <- false; BadL.secret <- (e0, e1);
      BadH.bad <- false; BadH.secret <- m;
      b' <@ A(BadH, BadL, K).guess(pk, c, k);
      return b';
  }}.

  (* Game5: pk を構造化へ戻す = 乱択鍵ワールド  [G4<->G5 : QCCF 逆, クリーン] *)
  module Game5 = { proc main() : bool = {
    var sk, sigma, pk, m, e0, e1, eh, c, k, b';
    H2.init(); L.init(); K.init();
    (sk, sigma, pk) <@ Bike.keyGen();
    m <$ duniformM;
    (e0, e1) <@ H2.hash(m);
    eh <@ L.hash(e0, e1);
    c <- (e0 + e1 * pk, m + eh);
    k <$ duniformK;
    b' <@ A(H2, L, K).guess(pk, c, k);
    return b';
  } }.

  (* ---- ホップ補題(要証明) ----
     [G0<->G1] / [G4<->G5] : QCCF。クリーンな byequiv 還元。
        Red_cf(A) : CF_Dist を定義(distinguish(h): pk=h として以降を忠実に実行)。
        Pr[Game0]=Pr[DQCCF(Red_cf_real(A)).main(false)],
        Pr[Game1]=Pr[DQCCF(Red_cf_real(A)).main(true)] を byequiv で示し引き算。
        レシピ: byequiv=>//; proc; inline*; swap で位置合わせ; call(_:true); auto.
        (HQC の hop1_left/right を写経)
     [G1<->G2] : ★ c0 は QCSD で一様化できるが c1=m+L(e0,e1) のマスクが
        (e0,e1) と結合している。QCSD 還元 + L の ROM 論法に分解が必要。
        単一 byequiv 等式にはならない(要相談)。暫定上界は eps_qcsd + eps_rom。
     [G2<->G3] : ROM。c0 一様→(e0,e1)隠れ→m 隠れ→K(m,c) は新鮮な RO 出力。
        A が K を (m,c) で引く確率 <= eps_rom(= qK*2^-l)。up-to-bad / fel。
      合計: 2*eps_qccf + 2*eps_qcsd + (ROM 項)。 *)

lemma G0_eq &m :
  Pr[Game0.main() @ &m : res] = Pr[DQCCF(Red_cf(A)).main(false) @&m : res].
proof.
  byequiv => //.
  proc.
  inline DQCCF(Red_cf(A)).main Red_cf(A).distinguish H2.init L.init K.init
         ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
  sim.
  wp; simplify.
  rnd{2}.
  call keyGen_eq; auto.
qed.

lemma G1_eq &m :
    Pr[Game1.main() @ &m : res] = Pr[DQCCF(Red_cf(A)).main(true) @ &m : res].
    proof.
    byequiv => //.
      proc.
      inline DQCCF(Red_cf(A)).main Red_cf(A).distinguish H2.init L.init K.init
         ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
      sim.
      wp.
      rnd.
      call{2} keyGen_ll.
      auto.
  qed.

  lemma G3_bad_c_c1 &m :
      Pr[Game3_bad_c.main() @ &m : BadHc.bad] = Pr[Game3_bad_c1.main() @ &m : BadHc.bad].
      proof.
      byequiv => //.
        proc.
        call (_: ={glob H2, glob L, glob K, glob BadHc}).
        + proc; inline*; auto.
        + proc; inline*; auto.
        + proc; inline*; auto.
       inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
wp.
rnd.                                   (* k <$ duniformK : 両側同一 → 恒等 *)
wp.                                    (* c <- (.., m+lmask) / c <- (.., c1) *)
rnd (fun (lmask : M) => m{1} + lmask)
    (fun (c1 : M)    => c1 - m{1}).      (* OTP を本来の lmask/c1 に *)
auto => />.
smt(vec_subrK vec_subrK2 vec_subv_supp duniformM_funi duniformM_size
      size_oppv size_addv duniformK_dvec).
    qed.

    lemma G3_bad_c1e_q &m :
  Pr[Game3_bad_c1e.main() @ &m : res] = Pr[Game3_bad_q.main() @ &m : res].
proof.
  byequiv => //.
  proc.
  swap{1} 5 9.   (* ★ `m <$ duniformM` を guess の直前まで下げる。位置は実機の左カラムで数えて差し替え ★ *)
  sim.
qed.
  
lemma G4_eq &m :
    Pr[Game4.main() @ &m : res] = Pr[DQCCF(Red_cf_rand(A)).main(true) @ &m : res].
    proof.
    byequiv => //.
      proc.
      inline DQCCF(Red_cf_rand(A)).main Red_cf_rand(A).distinguish H2.init L.init K.init
         ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
      sim.
      wp.
      rnd.
      call{2} keyGen_ll.
      auto.
  qed.

  lemma G5_eq &m :
      Pr[Game5.main() @ &m : res] = Pr[DQCCF(Red_cf_rand(A)).main(false) @ &m : res].
      proof.
      byequiv => //.
        proc.
        inline DQCCF(Red_cf_rand(A)).main Red_cf_rand(A).distinguish H2.init L.init K.init
         ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
        sim.
        wp.
        simplify.
        rnd{2}.
        call keyGen_eq.
        auto.
    qed.

  lemma G0_G1 &m :
      `| Pr[Game0.main() @ &m : res] - Pr[Game1.main() @ &m : res] | <= eps_qccf.
      proof. rewrite (G0_eq &m) (G1_eq &m); exact (qccf_hard &m (Red_cf(A))). qed.

  lemma G1_G1_bad &m : Pr[Game1.main() @ &m : res] = Pr[Game1_bad.main() @ &m : res].
      proof.
      byequiv => //.
        proc.
        call (_: ={glob H2, glob L, glob K}).
        + proc*; inline{2} BadH.hash; wp; call H2_hash_eq; auto.
        + proc*; inline{2} BadL.hash; wp; call L_hash_eq; auto.
        + proc; inline*; auto.
        inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
        wp.
        call K_hash_eq.
        wp.
        call L_hash_eq.
        call H2_hash_eq.
        auto.
    qed.

  lemma G2_G2_bad &m : Pr[Game2.main() @ &m : res] = Pr[Game2_bad.main() @ &m : res].
      proof.
      byequiv => //.
        proc.
        call (_: ={glob H2, glob L, glob K}).
        + proc*; inline{2} BadH.hash; wp; call H2_hash_eq; auto.
        + proc*; inline{2} BadL.hash; wp; call L_hash_eq; auto.
        + proc; inline*; auto.
        inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
        wp.
        call K_hash_eq.
        auto.
    qed.

  lemma G1_bad_G2_bad_upto :
  equiv[Game1_bad.main ~ Game2_bad.main :
        ={glob A} ==> !(BadL.bad{2} \/ BadH.bad{2}) => ={res}].
      proof.
        proc.
        call (_: BadL.bad \/ BadH.bad,
        ={ROK.Lazy.LRO.m, BadL.secret, BadH.secret}
        /\ FMap.eq_except (pred1 BadL.secret{2}) ROL.Lazy.LRO.m{1} ROL.Lazy.LRO.m{2}
        /\ FMap.eq_except (pred1 BadH.secret{2}) ROH.Lazy.LRO.m{1} ROH.Lazy.LRO.m{2}).
        exact A_guess_ll.
        proc; inline H2.hash ROH.Lazy.LRO.o.
        if; 1: by auto.
        wp; rnd; auto => />; smt().
        wp; rnd; auto => />; smt(FMap.get_setE FMap.get_set_neqE FMap.eq_except_set_eq FMap.eq_exceptP FMap.domNE).
      move=> *; proc; call H2_hash_ll; auto.
      move=> *; proc; call H2_hash_ll; auto.
        proc; inline L.hash ROL.Lazy.LRO.o.
        if; 1: by auto.
        wp; rnd; auto => />; smt().
        wp; rnd; auto => />; smt(FMap.get_setE FMap.get_set_neqE FMap.eq_except_set_eq FMap.eq_exceptP FMap.domNE).
      move=> *; proc; call L_hash_ll; auto.
      move=> *; proc; call L_hash_ll; auto.
        proc; inline K.hash ROK.Lazy.LRO.o; auto => />.
      move=> *; proc; inline ROK.Lazy.LRO.o; auto => />; smt(duniformM_ll).
      move=> *; proc; inline ROK.Lazy.LRO.o; auto => />; smt(duniformM_ll).
          wp.
          call K_hash_eq.
          wp.
          inline{1} H2.hash L.hash ROH.Lazy.LRO.o ROL.Lazy.LRO.o.
          rcondt{1} 9.
      by move=> &m; inline*; auto => />; smt(FMap.mem_empty).
          rcondt{1} 15.
      by move=> &m; inline*; auto => />; smt(FMap.mem_empty).
          inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
          wp.
          rnd.
          wp.
          rnd.
          wp.
          rnd.
          rnd.
      auto => />.
          smt(FMap.get_set_sameE FMap.eq_except_setl).
    qed.

  lemma G1_bad_G2_bad &m :
      `| Pr[Game1_bad.main() @ &m : res] - Pr[Game2_bad.main() @ &m : res] |
      <= Pr[Game2_bad.main() @ &m : BadL.bad \/ BadH.bad].
      proof.
        have d1 : Pr[Game1_bad.main() @ &m : res]
        <= Pr[Game2_bad.main() @ &m : res \/ (BadL.bad \/ BadH.bad)].
      byequiv => //.
        conseq G1_bad_G2_bad_upto; smt().
        have d2 : Pr[Game2_bad.main() @ &m : res /\ !(BadL.bad \/ BadH.bad)]
        <= Pr[Game1_bad.main() @ &m : res].
      byequiv => //.
        symmetry.
        conseq G1_bad_G2_bad_upto; smt().
        have or3 : Pr[Game2_bad.main() @ &m : res \/ (BadL.bad \/ BadH.bad)]
        <= Pr[Game2_bad.main() @ &m : res] + Pr[Game2_bad.main() @ &m : BadL.bad \/ BadH.bad].
        rewrite Pr[mu_or]; smt(mu_bounded).
        have sp3 : Pr[Game2_bad.main() @ &m : res]
      = Pr[Game2_bad.main() @ &m : res /\ !(BadL.bad \/ BadH.bad)] + Pr[Game2_bad.main() @ &m : res /\ (BadL.bad \/ BadH.bad)].
        rewrite Pr[mu_split (BadL.bad \/ BadH.bad)]; smt().
        have b3 : Pr[Game2_bad.main() @ &m : res /\ (BadL.bad \/ BadH.bad)]
        <= Pr[Game2_bad.main() @ &m : BadL.bad \/ BadH.bad].
        rewrite Pr[mu_sub] //.
        smt().
    qed.

  lemma G2_G2_bK &m : Pr[Game2.main() @ &m : res] = Pr[Game2_bK.main() @ &m : res].
      proof.
      byequiv => //.
        proc.
        call (_: ={glob H2, glob L, glob K}).
        + proc; inline*; auto.
        + proc; inline*; auto.
        + proc*; inline{2} BadK.hash; wp; call K_hash_eq; auto.
        inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
        wp.
        call K_hash_eq.
        auto.
    qed.

  lemma G3_G3_bK &m : Pr[Game3.main() @ &m : res] = Pr[Game3_bK.main() @ &m : res].
      proof.
      byequiv => //.
        proc.
        call (_: ={glob H2, glob L, glob K}).
        + proc; inline*; auto.
        + proc; inline*; auto.
        + proc*; inline{2} BadK.hash; wp; call K_hash_eq; auto.
        inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
        wp.
        rnd.
        auto.
    qed.

  lemma G2_bK_G3_bK_upto :
  equiv[Game2_bK.main ~ Game3_bK.main :
        ={glob A} ==> !BadK.bad{2} => ={res}].
      proof.
        proc.
        call (_: BadK.bad,
        ={ROH.Lazy.LRO.m, ROL.Lazy.LRO.m, BadK.secret}
        /\ FMap.eq_except (pred1 BadK.secret{2}) ROK.Lazy.LRO.m{1} ROK.Lazy.LRO.m{2}).
        exact A_guess_ll.
        proc; inline ROH.Lazy.LRO.o; auto => />.
      move=> *; proc; inline ROH.Lazy.LRO.o; auto => />; smt(DEt_ll).
      move=> *; proc; inline ROH.Lazy.LRO.o; auto => />; smt(DEt_ll).
          proc; inline ROL.Lazy.LRO.o; auto => />.
      move=> *; proc; inline ROL.Lazy.LRO.o; auto => />; smt(duniformM_ll).
      move=> *; proc; inline ROL.Lazy.LRO.o; auto => />; smt(duniformM_ll).
      proc; inline K.hash ROK.Lazy.LRO.o.
        if; 1: by auto.
        wp; rnd; auto => />; smt().
        wp; rnd; auto => />; smt(FMap.get_setE FMap.get_set_neqE FMap.eq_except_set_eq FMap.eq_exceptP FMap.domNE).
      move=> *; proc; call K_hash_ll; auto.
      move=> *; proc; call K_hash_ll; auto.
        wp.
        inline{1} K.hash ROK.Lazy.LRO.o.
        rcondt{1} 12.
      by move=> &m; inline*; auto => />; smt(FMap.mem_empty).
        inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
        wp.
        rnd.
        wp.
        rnd.
        rnd.
        rnd.
        rnd.
      auto => />.
        smt(FMap.get_set_sameE FMap.eq_except_setl).
    qed.

  lemma G2_bK_G3_bK &m :
      `| Pr[Game2_bK.main() @ &m : res] - Pr[Game3_bK.main() @ &m : res] |
      <= Pr[Game3_bK.main() @ &m : BadK.bad].
      proof.
        have d1 : Pr[Game2_bK.main() @ &m : res] <= Pr[Game3_bK.main() @ &m : res \/ BadK.bad].
      byequiv => //.
        conseq G2_bK_G3_bK_upto; smt().
        have d2 : Pr[Game3_bK.main() @ &m : res /\ !BadK.bad] <= Pr[Game2_bK.main() @ &m : res].
      byequiv => //.
        symmetry.
        conseq G2_bK_G3_bK_upto; smt().
        have or3 : Pr[Game3_bK.main() @ &m : res \/ BadK.bad]
        <= Pr[Game3_bK.main() @ &m : res] + Pr[Game3_bK.main() @ &m : BadK.bad].
        rewrite Pr[mu_or]; smt(mu_bounded).
        have sp3 : Pr[Game3_bK.main() @ &m : res]
      = Pr[Game3_bK.main() @ &m : res /\ !BadK.bad] + Pr[Game3_bK.main() @ &m : res /\ BadK.bad].
        rewrite Pr[mu_split BadK.bad]; smt().
        have b3: Pr[Game3_bK.main() @ &m : res /\ BadK.bad] <= Pr[Game3_bK.main() @ &m : BadK.bad].
        rewrite Pr[mu_sub] //.
        smt().
    qed.

  lemma G3_G3_bad &m : Pr[Game3.main() @ &m : res] = Pr[Game3_bad.main() @ &m : res].
      proof.
      byequiv => //.
        proc.
        call (_: ={glob H2, glob L, glob K}).
        + proc*; inline{2} BadH.hash; wp; call H2_hash_eq; auto.
        + proc*; inline{2} BadL.hash; wp; call L_hash_eq; auto.
        + proc; inline*; auto.
        inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
        wp.
        rnd.
        auto.
    qed.

    lemma G3_bK_G3_bK_c &m :
  Pr[Game3_bK.main() @ &m : BadK.bad] = Pr[Game3_bK_c.main() @ &m : BadKc.bad].
proof.
  byequiv => //.
  proc.
  call (_: ={glob H2, glob L, glob K}
           /\ BadK.bad{1} = BadKc.bad{2}
           /\ BadK.secret{1} = BadKc.secret{2}).
  + (* OH = H2.hash 両側 *)
    proc; inline*; auto.
  + (* OL = L.hash 両側 *)
    proc; inline*; auto.
  + (* OK: BadK.hash {1} ~ BadKc.hash {2} *)
    proc; inline K.hash ROK.Lazy.LRO.o.
    if; 1: by auto.
    - sim.
    - sim.
  inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
  wp.
  rnd.
  auto => />.
qed.

lemma G3_bK_c_c1 &m :
  Pr[Game3_bK_c.main() @ &m : BadKc.bad] = Pr[Game3_bK_c1.main() @ &m : BadKc.bad].
proof.
  byequiv => //.
  proc.
  call (_: ={glob H2, glob L, glob K, glob BadKc}).
  + proc; inline*; auto.
  + proc; inline*; auto.
  + proc; inline*; auto.
  inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
  wp.
  rnd.                                   (* k <$ duniformK : 両側同一 → 恒等 *)
  wp.                                    (* c <- (.., m+lmask) / c <- (.., c1) *)
  rnd (fun (lmask : M) => m{1} + lmask)
      (fun (c1 : M)    => c1 - m{1}).      (* OTP を本来の lmask/c1 に *)
  auto => />.
  smt(vec_subrK vec_subrK2 vec_subv_supp duniformM_funi duniformM_size
        size_oppv size_addv duniformK_dvec).
    qed.

lemma G3_bK_c1_le_c1e_upto :
  equiv[Game3_bK_c1.main ~ Game3_bK_c1e.main :
        ={glob A} ==> BadKc.bad{1} => res{2}].
proof.
  proc.
  call (_: ={glob H2, glob L, glob K, BadKc.qs, BadKc.cnt}
           /\ (BadKc.bad{1} => BadKc.secret{1} \in BadKc.qs{1})).
  + proc; inline*; auto.
  + proc; inline*; auto.
  + proc; inline K.hash ROK.Lazy.LRO.o.
    if{1}; if{2}; auto => />; smt(mem_rcons).
  inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
  wp. rnd. wp. rnd. rnd. rnd. rnd.
  auto => />.
  smt(mem_map map_f mapP).
qed.

lemma G3_bK_c1_le_c1e &m :
  Pr[Game3_bK_c1.main() @ &m : BadKc.bad] <= Pr[Game3_bK_c1e.main() @ &m : res].
proof. byequiv G3_bK_c1_le_c1e_upto => //. qed.

lemma G3_bK_c1e_q &m :
  Pr[Game3_bK_c1e.main() @ &m : res] = Pr[Game3_bK_q.main() @ &m : res].
proof.
  byequiv => //.
  proc.
  swap{1} 5 9.   (* ★ m <$ duniformM を guess 後へ。本数は実機の左カラムで要調整 ★ *)
  sim.
qed.

lemma G3_bK_c1_le_q &m :
  Pr[Game3_bK_c1.main() @ &m : BadKc.bad] <= Pr[Game3_bK_q.main() @ &m : res].
  proof. rewrite -(G3_bK_c1e_q &m); exact (G3_bK_c1_le_c1e &m). qed.

lemma GqK_bnd :
  phoare[ Game3_bK_q.main : true ==> res ] <= (qK%r / (2^l)%r).
proof.
  proc.
  seq 13 : (size BadKc.qs <= qK) 1%r (qK%r / (2^l)%r) 0%r 1%r.
  + by conseq (: _ ==> true) => //.        (* 到達R枝 *)
  + by conseq (: _ ==> true) => //.        (* !R後段枝 *)
  + rnd.                                    (* 本体枝 *)
    skip => &hr hsz.
    have hb : forall (x : M), mu1 duniformM x <= 1%r/(2^l)%r
      by move=> x; exact mu1_duniformM_le.
    have h1 := mu_mem_le_mu1 duniformM
                 (map (fun (x : M * R * M) => x.`1) BadKc.qs{hr})
                 (1%r/(2^l)%r) hb.
    have hszmap : size (map (fun (x : M * R * M) => x.`1) BadKc.qs{hr})
                  = size BadKc.qs{hr} by rewrite size_map.
    have h2 : (size BadKc.qs{hr})%r * (1%r/(2^l)%r) <= qK%r / (2^l)%r.
    + have hpos : 0%r < (2^l)%r by smt(StdOrder.IntOrder.expr_gt0).
      have hsz' : (size BadKc.qs{hr})%r <= qK%r by smt(le_fromint).
      smt().
    smt(size_map).
  (* !R枝: phoare[ (1)-(13) : true ==> !(size qs<=qK) ] <= 0%r *)
  hoare.
  simplify.
  call A_qK_bound.
  inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
  auto.
  smt().
qed.

lemma GqK_rom &m : Pr[Game3_bK_q.main() @ &m : res] <= qK%r / (2^l)%r.
proof. byphoare (_: true ==> res) => //. exact GqK_bnd. qed.

  lemma G4_G4_bad &m : Pr[Game4.main() @ &m : res] = Pr[Game4_bad.main() @ &m : res].
      proof.
      byequiv => //.
        proc.
        call (_: ={glob H2, glob L, glob K}).
        + proc*; inline{2} BadH.hash; wp; call H2_hash_eq; auto.
        + proc*; inline{2} BadL.hash; wp; call L_hash_eq; auto.
        + proc*; inline*; auto.
        inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
        wp.
        rnd.
        wp.
        call L_hash_eq.
        call H2_hash_eq.
        auto.
    qed.

  lemma G3_bad_G4_bad_upto :
  equiv[Game4_bad.main ~ Game3_bad.main :
        ={glob A} ==> !(BadL.bad{2} \/ BadH.bad{2}) => ={res}].
      proof.
        proc.
        call (_: BadL.bad \/ BadH.bad,
        ={ROK.Lazy.LRO.m, BadL.secret, BadH.secret}
          /\ FMap.eq_except (pred1 BadL.secret{2}) ROL.Lazy.LRO.m{1} ROL.Lazy.LRO.m{2}
          /\ FMap.eq_except (pred1 BadH.secret{2}) ROH.Lazy.LRO.m{1} ROH.Lazy.LRO.m{2}).
          exact A_guess_ll.
          proc; inline H2.hash ROH.Lazy.LRO.o.
          if; 1: by auto.
          wp; rnd; auto => />; smt().
          wp; rnd; auto => />; smt(FMap.get_setE FMap.get_set_neqE FMap.eq_except_set_eq FMap.eq_exceptP FMap.domNE).
      move=> *; proc; call H2_hash_ll; auto.
      move=> *; proc; call H2_hash_ll; auto.
          proc; inline L.hash ROL.Lazy.LRO.o.
          if; 1: by auto.
          wp; rnd; auto => />; smt().
          wp; rnd; auto => />; smt(FMap.get_setE FMap.get_set_neqE FMap.eq_except_set_eq FMap.eq_exceptP FMap.domNE).
      move=> *; proc; call L_hash_ll; auto.
      move=> *; proc; call L_hash_ll; auto.
          proc; inline K.hash ROK.Lazy.LRO.o; auto => />.
      move=> *; proc; inline ROK.Lazy.LRO.o; auto => />; smt(duniformM_ll).
      move=> *; proc; inline ROK.Lazy.LRO.o; auto => />; smt(duniformM_ll).
          wp.
          rnd.
          wp.
          inline{1} H2.hash L.hash ROH.Lazy.LRO.o ROL.Lazy.LRO.o.
          rcondt{1} 9.
      by move=> *; inline*; auto => />; smt(FMap.mem_empty).
          rcondt{1} 15.
      by move=> *; inline*; auto => />; smt(FMap.mem_empty).
          inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
          wp.
          rnd.
          wp.
          rnd.
          wp.
          rnd.
          rnd.
      auto => />.
          smt(FMap.get_set_sameE FMap.eq_except_setl).
    qed.

  lemma G3_bad_G4_bad &m :
      `| Pr[Game3_bad.main() @ &m : res] - Pr[Game4_bad.main() @ &m : res] |
      <= Pr[Game3_bad.main() @ &m : BadL.bad \/ BadH.bad].
      proof.
        have d1 : Pr[Game4_bad.main() @ &m : res]
        <= Pr[Game3_bad.main() @ &m : res \/ (BadL.bad \/ BadH.bad)].
      byequiv => //.
        conseq G3_bad_G4_bad_upto; smt().
        have d2 : Pr[Game3_bad.main() @ &m : res /\ !(BadL.bad \/ BadH.bad)]
        <= Pr[Game4_bad.main() @ &m : res].
      byequiv => //.
        symmetry.
        conseq G3_bad_G4_bad_upto; smt().
        have or3 : Pr[Game3_bad.main() @ &m : res \/ (BadL.bad \/ BadH.bad)]
        <= Pr[Game3_bad.main() @ &m : res] + Pr[Game3_bad.main() @ &m : BadL.bad \/ BadH.bad].
        rewrite Pr[mu_or]; smt(mu_bounded).
        have sp3 : Pr[Game3_bad.main() @ &m : res]
      = Pr[Game3_bad.main() @ &m : res /\ !(BadL.bad \/ BadH.bad)] + Pr[Game3_bad.main() @ &m : res /\ (BadL.bad \/ BadH.bad)].
        rewrite Pr[mu_split (BadL.bad \/ BadH.bad)]; smt().
        have b3 : Pr[Game3_bad.main() @ &m : res /\ (BadL.bad \/ BadH.bad)]
        <= Pr[Game3_bad.main() @ &m : BadL.bad \/ BadH.bad].
        rewrite Pr[mu_sub] //.
        smt().
    qed.
    
  lemma badL_fp_inv :
  hoare[DQCSD(Red_sd_bad(A)).main : arg = true ==>
        res =>
        Red_sd_bad.ss \in
        map (fun (x : R * R) => x.`1 + x.`2 * Red_sd_bad.hh) enumE_t].
proof.
  proc; inline Red_sd_bad(A).distinguish.
  wp.
  call (_: Red_sd_bad.found =>
           Red_sd_bad.ss \in
           map (fun (x : R * R) => x.`1 + x.`2 * Red_sd_bad.hh) enumE_t).
  - proc; inline ROH.Lazy.LRO.o; auto.
  - proc; inline L.hash ROL.Lazy.LRO.o.
    if; last by auto => />; smt().
    auto => />; smt(Et_complete map_f).
  - proc; inline ROK.Lazy.LRO.o; auto.
  inline K.hash ROK.Lazy.LRO.o H2.init L.init K.init
         ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
  auto => />.
qed.

lemma badL_fp_bnd :
  phoare[ DQCSD(Red_sd_bad(A)).main :
          arg = true ==>
          Red_sd_bad.ss \in
          map (fun (x : R * R) => x.`1 + x.`2 * Red_sd_bad.hh) enumE_t ] <= negl.
proof.
  proc; inline Red_sd_bad(A).distinguish.
  seq 13 : (Red_sd_bad.ss \in
            map (fun (x : R * R) => x.`1 + x.`2 * Red_sd_bad.hh) enumE_t)
           negl 1%r 1%r 0%r.
 + inline H2.init L.init K.init
           ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
    wp.
    rnd.
    auto => />.
    inline *.
    wp.
    rnd.
    auto => />.
    move=> h1 _ e0e1 _.
    have ->: mem (map (fun (x : Top.R * Top.R) => x.`1 + x.`2 * h1) enumE_t)
           = (fun (su : Top.R) =>
                su \in map (fun (x : Top.R * Top.R) => x.`1 + x.`2 * h1) enumE_t)
      by apply fun_ext.
             apply (fp_measure h1).
  + by conseq (: _ ==> true) => //.
           hoare.
    inline K.hash ROK.Lazy.LRO.o.
    wp.
    call (_: !(Red_sd_bad.ss \in
               map (fun (x : Top.R * Top.R) => x.`1 + x.`2 * Red_sd_bad.hh) enumE_t)).
    - by proc; inline ROH.Lazy.LRO.o; auto.
    - by proc; inline L.hash ROL.Lazy.LRO.o; auto.
    - by proc; inline ROK.Lazy.LRO.o; auto.
             auto.
           + smt().
         qed.

lemma badL_fp_inv' :
  hoare[DQCSD(Red_sd_rand_bad(A)).main : arg = true ==>
        res =>
        Red_sd_rand_bad.ss \in
        map (fun (x : R * R) => x.`1 + x.`2 * Red_sd_rand_bad.hh) enumE_t].
proof.
  proc; inline Red_sd_rand_bad(A).distinguish.
  wp.
  call (_: Red_sd_rand_bad.found =>
           Red_sd_rand_bad.ss \in
           map (fun (x : R * R) => x.`1 + x.`2 * Red_sd_rand_bad.hh) enumE_t).
  - proc; inline ROH.Lazy.LRO.o; auto.
  - proc; inline L.hash ROL.Lazy.LRO.o.
    if; last by auto => />; smt().
    auto => />; smt(Et_complete map_f).
  - proc; inline ROK.Lazy.LRO.o; auto.
  inline H2.init L.init K.init
         ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
  auto => />.
qed.

lemma badL_fp_bnd' :
  phoare[ DQCSD(Red_sd_rand_bad(A)).main :
          arg = true ==>
          Red_sd_rand_bad.ss \in
          map (fun (x : R * R) => x.`1 + x.`2 * Red_sd_rand_bad.hh) enumE_t ] <= negl.
proof.
  proc; inline Red_sd_rand_bad(A).distinguish.
  seq 13 : (Red_sd_rand_bad.ss \in
            map (fun (x : Top.R * Top.R) => x.`1 + x.`2 * Red_sd_rand_bad.hh) enumE_t)
           negl 1%r 1%r 0%r.
  by conseq (: _ ==> true) => //.
  inline *.
  wp.
  rnd.
  auto.
move=> &hr Hb h1 _ e0e1 _.
rewrite Hb /=.
apply (fp_measure h1).
  by conseq (: _ ==> true) => //.
hoare.
wp.
call (_: !(Red_sd_rand_bad.ss \in
           map (fun (x : Top.R * Top.R) => x.`1 + x.`2 * Red_sd_rand_bad.hh) enumE_t)).
- by proc; inline ROH.Lazy.LRO.o; auto.
- by proc; inline L.hash ROL.Lazy.LRO.o; auto.
- by proc; inline ROK.Lazy.LRO.o; auto.
  auto.
  smt().
qed.

lemma badL_fp &m :
  Pr[ DQCSD(Red_sd_bad(A)).main(true) @ &m : res ] <= negl.
proof.
  byphoare (_: arg = true ==> res) => //.
  conseq badL_fp_bnd badL_fp_inv; smt().
qed.

lemma badL_fp' &m :
  Pr[DQCSD(Red_sd_rand_bad(A)).main(true) @ &m : res] <= negl.
proof.
  byphoare (_: arg = true ==> res) => //.
  conseq badL_fp_bnd' badL_fp_inv'; smt().
qed.

lemma G3_bad_G3_bad_c &m :
      Pr[Game3_bad.main() @ &m : BadH.bad] = Pr[Game3_bad_c.main() @ &m : BadHc.bad].
      proof.
      byequiv => //.
        proc.
        call (_: ={glob H2, glob L, glob K}
                 /\ BadH.bad{1} = BadHc.bad{2}
                 /\ BadH.secret{1} = BadHc.secret{2}).
        + (* OH: BadH.hash {1} ~ BadHc.hash {2} *)
          proc; inline H2.hash ROH.Lazy.LRO.o.
          if; 1: by auto.
          - sim.
          - sim.
        + (* OL = L.hash 両側 *)
          proc; inline*; auto.
        + (* OK = K.hash 両側 *)
          proc; inline*; auto.
        inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
        wp.
        rnd.
        wp.
        rnd.
        rnd.
        rnd.
        rnd.
        auto => />.
    qed.

    lemma G3_bad_c1_c1e &m :
  Pr[Game3_bad_c1.main() @ &m : BadHc.bad] = Pr[Game3_bad_c1e.main() @ &m : res].
proof.
  byequiv => //.
  proc.
  call (_: ={glob H2, glob L, glob K, BadHc.qs, BadHc.cnt}
           /\ BadHc.bad{1} = (BadHc.secret{1} \in BadHc.qs{1})).
  + (* ★ OH: BadHc.hash。secret が m vs witness で if 条件が非対称 → if{1};if{2} ★ *)
    proc; inline H2.hash ROH.Lazy.LRO.o.
    if{1}; if{2}; auto => />; smt(mem_rcons).
  + proc; inline*; auto.
  + proc; inline*; auto.
  inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
  wp.
  rnd. wp. rnd. rnd. rnd. rnd.    (* G3_bad_G3_bad_c と同じ並び：k, c<-, c1, e0e1, m, pk *)
  auto => />.
qed.

lemma G3_bad_c1_q &m :
  Pr[Game3_bad_c1.main() @ &m : BadHc.bad] = Pr[Game3_bad_q.main() @ &m : res].
  proof. by rewrite (G3_bad_c1_c1e &m) (G3_bad_c1e_q &m). qed.

lemma Gq_bnd :
  phoare[ Game3_bad_q.main : true ==> res ] <= (qH%r / (2^l)%r).
proof.
  proc.
  seq 13 : (size BadHc.qs <= qH) 1%r (qH%r / (2^l)%r) 0%r 1%r.

  (* ── 1本目: 到達R  phoare[(1)-(13): true ==> size qs<=qH] <= 1%r ── *)
  (* ※ここが「到達R」か「本体」かは Bound と program で判定。program が (1)-(13) なら到達R。 *)
  + by conseq (: _ ==> true) => //.

  + by conseq (: _ ==> true) => //.

+ rnd.
skip => &hr hsz.
have hb : forall (x : M), mu1 duniformM x <= 1%r/(2^l)%r
  by move=> x; exact mu1_duniformM_le.
have h1 := mu_mem_le_mu1 duniformM BadHc.qs{hr} (1%r/(2^l)%r) hb.
have h2 : (size BadHc.qs{hr})%r * (1%r/(2^l)%r) <= qH%r / (2^l)%r.
+ have hpos : 0%r < (2^l)%r by smt(StdOrder.IntOrder.expr_gt0).
  have hsz' : (size BadHc.qs{hr})%r <= qH%r by smt(le_fromint).
  smt().
smt().

  (* ── 2本目: !R枝  phoare[(1)-(13): true ==> !(size qs<=qH)] <= 0%r ── *)
(* !R枝の頭（post = ! size qs<=qH）から *)
(* !R枝: phoare[ (1)-(13) : true ==> !(size qs<=qH) ] <= 0%r *)
hoare.
simplify.
call A_qH_bound.
inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
auto.
smt().
qed.

(* A: Game2_bad の OL=BadL→L, OK=K→BadK を同時透過。観測は BadH.bad *)
lemma G2bad_G2bad_bK &m :
  Pr[Game2_bad.main() @ &m : BadH.bad] = Pr[Game2_bad_bK.main() @ &m : BadH.bad].
proof.
  byequiv (_: ={glob A} ==> ={BadH.bad}) => //.
  proc.
  call (_: ={glob H2, glob L, glob K, glob BadH}).
  + (* OH: BadH ~ BadH（同一） *)
    proc; inline H2.hash ROH.Lazy.LRO.o.
    if; 1: by auto.
    - sim.
    - sim.
  + (* OL: BadL{1} ~ L{2}（左ラッパ） *)
    proc*; inline{1} BadL.hash; wp; call L_hash_eq; auto.
  + (* OK: K{1} ~ BadK{2}（右ラッパ） *)
    proc*; inline{2} BadK.hash; wp; call K_hash_eq; auto.
  inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
  wp.
  call K_hash_eq.
  auto.
qed.

(* B: Game3_bad 側。k は両側 duniformK なので prefix は rnd *)
lemma G3bad_G3bad_bK &m :
  Pr[Game3_bad.main() @ &m : BadH.bad] = Pr[Game3_bad_bK.main() @ &m : BadH.bad].
proof.
  byequiv (_: ={glob A} ==> ={BadH.bad}) => //.
  proc.
  call (_: ={glob H2, glob L, glob K, glob BadH}).
  + proc; inline H2.hash ROH.Lazy.LRO.o.
    if; 1: by auto.
    - sim.
    - sim.
  + proc*; inline{1} BadL.hash; wp; call L_hash_eq; auto.
  + proc*; inline{2} BadK.hash; wp; call K_hash_eq; auto.
  inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
  wp.
  rnd.
  auto.
qed.

(* C: Game3_bad_bK の OH=BadH→H2 を透過。観測は BadK.bad *)
lemma G3bad_bK_G3bK &m :
  Pr[Game3_bad_bK.main() @ &m : BadK.bad] = Pr[Game3_bK.main() @ &m : BadK.bad].
proof.
  byequiv (_: ={glob A} ==> ={BadK.bad}) => //.
  proc.
  call (_: ={glob H2, glob L, glob K, glob BadK}).
  + (* OH: BadH{1} ~ H2{2}（左ラッパ） *)
    proc*; inline{1} BadH.hash; wp; call H2_hash_eq; auto.
  + (* OL: L ~ L（同一） *)
    proc; inline*; auto.
  + (* OK: BadK ~ BadK（同一） *)
    proc; inline K.hash ROK.Lazy.LRO.o.
    if; 1: by auto.
    - sim.
    - sim.
  inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
  wp.
  rnd.
  auto.
qed.

lemma Gq_rom &m : Pr[Game3_bad_q.main() @ &m : res] <= qH%r / (2^l)%r.
proof. byphoare (_: true ==> res) => //. exact Gq_bnd. qed.

  lemma badH_rom' &m : Pr[Game3_bad.main() @ &m : BadH.bad] <= eps_rom.
proof.
  rewrite (G3_bad_G3_bad_c &m) (G3_bad_c_c1 &m) (G3_bad_c1_q &m).
  have h  := Gq_rom &m.
  have he := eps_rom_qH.
  smt().
qed.

lemma G2bad_bK_G3bad_bK_upto :
  equiv[Game2_bad_bK.main ~ Game3_bad_bK.main :
        ={glob A} ==> !BadK.bad{2} => ={BadH.bad}].
proof.
  proc.
  call (_: BadK.bad,
    ={ROH.Lazy.LRO.m, ROL.Lazy.LRO.m, BadH.bad, BadH.secret, BadK.secret}
    /\ FMap.eq_except (pred1 BadK.secret{2}) ROK.Lazy.LRO.m{1} ROK.Lazy.LRO.m{2}).
  exact A_guess_ll.
  (* OH = BadH（両側同一・ROH 完全同期） *)
  proc; inline H2.hash ROH.Lazy.LRO.o.
  if; 1: by auto.
  wp; rnd; auto => />.
  wp; rnd; auto => />.
  move=> *; proc; call H2_hash_ll; auto.
  move=> *; proc; call H2_hash_ll; auto.
  (* OL = L（両側同一） *)
  proc; inline ROL.Lazy.LRO.o; auto => />.
  move=> *; proc; inline ROL.Lazy.LRO.o; auto => />; smt(duniformM_ll).
  move=> *; proc; inline ROL.Lazy.LRO.o; auto => />; smt(duniformM_ll).
  (* OK = BadK（up-to-bad） *)
  proc; inline K.hash ROK.Lazy.LRO.o.
  if; 1: by auto.
  wp; rnd; auto => />; smt().
  wp; rnd; auto => />; smt(FMap.get_setE FMap.get_set_neqE FMap.eq_except_set_eq FMap.eq_exceptP FMap.domNE).
  move=> *; proc; call K_hash_ll; auto.
  move=> *; proc; call K_hash_ll; auto.
  wp.
  inline{1} K.hash ROK.Lazy.LRO.o.
  rcondt{1} 12.
  by move=> &m; inline*; auto => />; smt(FMap.mem_empty).
  inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
  wp.
  rnd.
  wp.
  rnd.
  rnd.
  rnd.
  rnd.
  auto => />.
  smt(FMap.get_set_sameE FMap.eq_except_setl).
qed.

lemma G2bad_bK_G3bad_bK &m :
  `| Pr[Game2_bad_bK.main() @ &m : BadH.bad] - Pr[Game3_bad_bK.main() @ &m : BadH.bad] |
  <= Pr[Game3_bad_bK.main() @ &m : BadK.bad].
proof.
  have d1 : Pr[Game2_bad_bK.main() @ &m : BadH.bad]
    <= Pr[Game3_bad_bK.main() @ &m : BadH.bad \/ BadK.bad].
  byequiv => //.
    conseq G2bad_bK_G3bad_bK_upto; smt().
  have d2 : Pr[Game3_bad_bK.main() @ &m : BadH.bad /\ !BadK.bad]
    <= Pr[Game2_bad_bK.main() @ &m : BadH.bad].
  byequiv => //.
    symmetry.
    conseq G2bad_bK_G3bad_bK_upto; smt().
  have or3 : Pr[Game3_bad_bK.main() @ &m : BadH.bad \/ BadK.bad]
    <= Pr[Game3_bad_bK.main() @ &m : BadH.bad] + Pr[Game3_bad_bK.main() @ &m : BadK.bad].
    rewrite Pr[mu_or]; smt(mu_bounded).
  have sp3 : Pr[Game3_bad_bK.main() @ &m : BadH.bad]
    = Pr[Game3_bad_bK.main() @ &m : BadH.bad /\ !BadK.bad]
    + Pr[Game3_bad_bK.main() @ &m : BadH.bad /\ BadK.bad].
    rewrite Pr[mu_split BadK.bad]; smt().
  have b3 : Pr[Game3_bad_bK.main() @ &m : BadH.bad /\ BadK.bad]
    <= Pr[Game3_bad_bK.main() @ &m : BadK.bad].
    rewrite Pr[mu_sub] //.
  smt().
qed.

  lemma badK_rom &m : Pr[Game3_bK.main() @ &m : BadK.bad] <= eps_rom.
proof.
  rewrite (G3_bK_G3_bK_c &m) (G3_bK_c_c1 &m).
  have h1 := G3_bK_c1_le_q &m.      (* <= Pr[Game3_bK_q : res] *)
  have h2 := GqK_rom &m.            (* <= qK/2^l *)
  have h3 := eps_rom_qK.            (* qK/2^l <= eps_rom *)
  smt().
qed.

    lemma Et_filter (x : R * R) : x \in distribution_over_E_t => filter_Et x.
      proof.
        rewrite /distribution_over_E_t supp_duniform /enumE_t mem_filter; smt().
    qed.

  lemma badL_eq &m :
      Pr[Game2_bad.main() @ &m : BadL.bad]
        <= Pr[DQCSD(Red_sd_bad(A)).main(false) @ &m : res].
      proof.
        byequiv (_: ={glob A}  /\ arg{2} = false ==> BadL.bad{1} => res{2}) => //.
        proc.
        inline DQCSD(Red_sd_bad(A)).main Red_sd_bad(A).distinguish.
        wp.
        call (_: ={ROH.Lazy.LRO.m, ROL.Lazy.LRO.m, ROK.Lazy.LRO.m}
        /\ Red_sd_bad.ss{2} = BadL.secret{1}.`1 + BadL.secret{1}.`2 * Red_sd_bad.hh{2}
        /\ filter_Et BadL.secret{1}
        /\ (BadL.bad{1} => Red_sd_bad.found{2})).
        proc.
        if{1}.
        + sp 1 0; inline H2.hash ROH.Lazy.LRO.o; auto => />; smt().
        + inline H2.hash ROH.Lazy.LRO.o; auto => />; smt().
        proc.
        if{1}.
        + rcondt{2} 1; first by auto; smt().
        wp; call L_hash_eq; auto => />; smt().
        + if{2}.
        + wp; call L_hash_eq; auto => />; smt().
        + wp; call L_hash_eq; auto => />; smt().
        proc; inline K.hash ROK.Lazy.LRO.o; auto => />; smt().
        inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
        wp.
        call K_hash_eq.
        wp.
        swap{1} 5 1.
        rnd.
        rnd.
        wp.
        rnd{2}.
        wp.
        rnd.
        rnd.
      auto => />.
        smt(Et_filter).
    qed.

     lemma badL_eq' &m :
      Pr[Game3_bad.main() @ &m : BadL.bad]
        <= Pr[DQCSD(Red_sd_rand_bad(A)).main(false) @ &m : res].
      proof.
        byequiv (_: ={glob A} /\ arg{2} = false ==> BadL.bad{1} => res{2}) => //.
        proc.
        inline DQCSD(Red_sd_rand_bad(A)).main Red_sd_rand_bad(A).distinguish.
        wp.
        call (_: ={ROH.Lazy.LRO.m, ROL.Lazy.LRO.m, ROK.Lazy.LRO.m}
        /\ Red_sd_rand_bad.ss{2} = BadL.secret{1}.`1 + BadL.secret{1}.`2 * Red_sd_rand_bad.hh{2}
        /\ filter_Et BadL.secret{1}
        /\ (BadL.bad{1} => Red_sd_rand_bad.found{2})).
        proc.
        if{1}.
        + sp 1 0; inline H2.hash ROH.Lazy.LRO.o; auto => />; smt().
        + inline H2.hash ROH.Lazy.LRO.o; auto => />; smt().
        proc.
        if{1}.
        + rcondt{2} 1; first by auto; smt().
        wp; call L_hash_eq; auto => />; smt().
        + if{2}.
        + wp; call L_hash_eq; auto => />; smt().
        + wp; call L_hash_eq; auto => />; smt().
        proc; inline K.hash ROK.Lazy.LRO.o; auto => />; smt().
        inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
        wp.
        rnd.
        wp.
        swap{1} 5 1.
        rnd.
        rnd.
        wp.
        rnd{2}.
        wp.
        rnd.
        rnd.
      auto => />.
        smt(Et_filter).
    qed.

     lemma badL_qcsd' &m : Pr[Game3_bad.main() @ &m : BadL.bad] <= eps_qcsd + negl.
      proof.
        have h0 := badL_eq' &m.
        have hfp := badL_fp' &m.
        have hd := qcsd_hard &m (Red_sd_rand_bad(A)).
        smt().
    qed.

  lemma badL_qcsd &m : Pr[Game2_bad.main() @ &m : BadL.bad] <= eps_qcsd + negl.
      proof.
        have h0 := badL_eq &m.
        have hfp := badL_fp &m.
        have hd := qcsd_hard &m (Red_sd_bad(A)).
        smt().
    qed.



    lemma badH_raw &m : Pr[Game3_bad.main() @ &m : BadH.bad] <= qH%r / (2^l)%r.
proof.
  rewrite (G3_bad_G3_bad_c &m) (G3_bad_c_c1 &m) (G3_bad_c1_q &m).
  exact (Gq_rom &m).
qed.

lemma badK_raw &m : Pr[Game3_bK.main() @ &m : BadK.bad] <= qK%r / (2^l)%r.
proof.
  rewrite (G3_bK_G3_bK_c &m) (G3_bK_c_c1 &m).
  have h1 := G3_bK_c1_le_q &m.
  have h2 := GqK_rom &m.
  smt().
qed.

  lemma badH_rom &m : Pr[Game2_bad.main() @ &m : BadH.bad] <= eps_rom.
proof.
  have step :
    Pr[Game2_bad.main() @ &m : BadH.bad] <= qH%r / (2^l)%r + qK%r / (2^l)%r.
  + rewrite (G2bad_G2bad_bK &m).
    have hbridge := G2bad_bK_G3bad_bK &m.
    have hH : Pr[Game3_bad_bK.main() @ &m : BadH.bad] <= qH%r / (2^l)%r.
    + rewrite -(G3bad_G3bad_bK &m); exact (badH_raw &m).
    have hK : Pr[Game3_bad_bK.main() @ &m : BadK.bad] <= qK%r / (2^l)%r.
    + rewrite (G3bad_bK_G3bK &m); exact (badK_raw &m).
    smt().
  have hagg := eps_rom_qHK.
  have : qH%r / (2^l)%r + qK%r / (2^l)%r = (qH + qK)%r / (2^l)%r by smt().
  smt().
qed.

  lemma G1_G2 &m :
      `| Pr[Game1.main() @ &m : res] - Pr[Game2.main() @ &m : res] |
      <= eps_qcsd + eps_rom + negl.
      proof.
        rewrite (G1_G1_bad &m) (G2_G2_bad &m).
        have hf := G1_bad_G2_bad &m.
        have hor : Pr[Game2_bad.main() @ &m : BadL.bad \/ BadH.bad]
        <= Pr[Game2_bad.main() @ &m : BadL.bad] + Pr[Game2_bad.main() @ &m : BadH.bad].
        + rewrite Pr[mu_or]; smt(mu_bounded).
        have hL := badL_qcsd &m.
        have hH := badH_rom &m.
        smt().
    qed.

  lemma G2_G3 &m :
      `| Pr[Game2.main() @ &m : res] - Pr[Game3.main() @ &m : res] | <= eps_rom.
      proof.
        rewrite (G2_G2_bK &m) (G3_G3_bK &m).
        have h := G2_bK_G3_bK &m.
        have hbad := badK_rom &m.
        smt().
    qed.

  lemma G3_G4 &m :
      `| Pr[Game3.main() @ &m : res] - Pr[Game4.main() @ &m : res] |
      <= eps_qcsd + eps_rom + negl.
      proof.
        rewrite (G3_G3_bad &m) (G4_G4_bad &m).
        have hf := G3_bad_G4_bad &m.
        have hor : Pr[Game3_bad.main() @ &m : BadL.bad \/ BadH.bad]
        <= Pr[Game3_bad.main() @ &m : BadL.bad] + Pr[Game3_bad.main() @ &m : BadH.bad].
        + rewrite Pr[mu_or]; smt(mu_bounded).
        have hL := badL_qcsd' &m.
        have hH := badH_rom' &m.
        smt().
    qed.

  lemma G4_G5 &m :
    `| Pr[Game4.main() @ &m : res] - Pr[Game5.main() @ &m : res] | <= eps_qccf.
      proof.
        rewrite (G4_eq &m) (G5_eq &m).
        have H := qccf_hard &m (Red_cf_rand(A)).
        smt().
    qed.

  lemma BIKE_KEM_IND_CPA &m :
      `| Pr[Game0.main() @ &m : res] - Pr[Game5.main() @ &m : res] |
      <= 2%r*eps_qccf + 2%r*eps_qcsd + 3%r*eps_rom + 2%r*negl.
      proof.
        have h01 := G0_G1 &m.
        have h12 := G1_G2 &m.
        have h23 := G2_G3 &m.
        have h34 := G3_G4 &m.
        have h45 := G4_G5 &m.
        smt().
    qed.

end section Security.
