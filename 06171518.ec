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

clone MFinite as RFinite with type t <- R, op Support.enum <- enumR proof *.
realize Support.enum_spec. admitted.   (* [要証明] *)
op distribution_over_R = RFinite.dunifin.

clone MFinite as E_tFinite with type t <- (R * R), op Support.enum <- enumE_t proof *.
realize Support.enum_spec. admitted.   (* [要証明] *)
op distribution_over_E_t = E_tFinite.dunifin.

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

module Red_sd (A : Adv) : SD_Dist = {
  proc distinguish(h : R, s : R) : bool = {
  var m, lmask, c, k, b';
  H2.init(); L.init(); K.init();
  m <$ duniformM;
      lmask <$ duniformM;
      c <- (s, m + lmask);
      k <@ K.hash(m, c.`1, c.`2);
      b' <@ A(H2, L, K).guess(h, c, k);
      return b';
  }
}.

module Red_sd_rand (A : Adv) : SD_Dist = {
  proc distinguish(h : R, s : R) : bool = {
  var m, lmask, c, k, b';
  H2.init(); L.init(); K.init();
  m <$ duniformM;
  lmask <$ duniformM;
  c <- (s, m + lmask);
  k <$ duniformK;
  b' <@ A(H2, L, K).guess(h, c, k);
  return b';
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

lemma DEt_ll : is_lossless distribution_over_E_t.
    proof. rewrite /distribution_over_E_t; exact E_tFinite.dunifin_ll.
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

lemma H2_hash_eq :
equiv[H2.hash ~ H2.hash : = {arg, ROH.Lazy.LRO.m} ==> ={res, ROH.Lazy.LRO.m}].
    proof. proc; inline ROH.Lazy.LRO.o; auto => />. qed.

lemma K_hash_eq :
equiv[K.hash ~ K.hash : ={arg, ROK.Lazy.LRO.m} ==> ={res, ROK.Lazy.LRO.m}].
    proof. proc; inline ROK.Lazy.LRO.o; auto => />. qed.

section Security.
  declare module A <: Adv {-Bike, -K, -L, -H2, -Algorithm2, -Algorithm3, -ROK.Lazy.LRO, -ROL.Lazy.LRO, -ROSHAKE.Lazy.LRO, -ROH.Lazy.LRO, -BadK, -BadL, -BadH}.

  declare axiom qccf_hard &m (D <: CF_Dist) :
    `| Pr[DQCCF(D).main(false) @ &m : res] - Pr[DQCCF(D).main(true) @ &m : res] | <= eps_qccf.
  declare axiom qcsd_hard &m (D <: SD_Dist) :
    `| Pr[DQCSD(D).main(false) @ &m : res] - Pr[DQCSD(D).main(true) @ &m : res] | <= eps_qcsd.

  declare axiom A_guess_ll (OH <: OrclH{-A}) (OL <: OrclL{-A}) (OK <: OrclK{-A}) :
    islossless OH.hash => islossless OL.hash => islossless OK.hash =>
    islossless A(OH, OL, OK).guess.

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

module Game1_25 = { proc main() : bool = {
  var pk, m, e0, e1, lmask, c, k, b';
  H2.init(); L.init(); K.init();
  pk <$ distribution_over_R;
  m <$ duniformM;
    (e0, e1) <@ H2.hash(m);
      lmask <$ duniformM;
      c <- (e0 + e1 * pk, m + lmask);
      k <@ K.hash(m, c.`1, c.`2);
      b' <@ A(H2, L, K).guess(pk, c, k);
      return b';
  }}.

module Game1b = { proc main() : bool = {
  var pk, m, e0, e1, eh, c, k, b';
  H2.init(); L.init(); K.init();
  pk <$ distribution_over_R;
  m <$ duniformM;
    (e0, e1) <@ H2.hash(m);
      eh <@ L.hash(e0, e1);
      c <- (e0 + e1 * pk, m + eh);
      k <@ K.hash(m, c.`1, c.`2);
      BadL.bad <- false;
      BadL.secret <- (e0, e1);
      b' <@ A(H2, BadL, K).guess(pk, c, k);
      return b';
  }}.

module Game1_25b = { proc main() : bool = {
  var pk, m, e0, e1, lmask, c, k, b';
  H2.init(); L.init(); K.init();
  pk <$ distribution_over_R;
  m <$ duniformM;
    (e0, e1) <@ H2.hash(m);
      lmask <$ duniformM;
  c <- (e0 + e1 * pk, m + lmask);
  k <@ K.hash(m, c.`1, c.`2);
  BadL.bad <- false;
  BadL.secret <- (e0, e1);
  b' <@ A(H2, BadL, K).guess(pk, c, k);
  return b';
  }}.

module Game1_25h = { proc main() : bool = {
  var pk, m, e0, e1, lmask, c, k, b';
  H2.init(); L.init(); K.init();
  pk <$ distribution_over_R;
  m <$ duniformM;
    (e0, e1) <@ H2.hash(m);
      lmask <$ duniformM;
      c <- (e0 + e1 * pk, m + lmask);
      k <@ K.hash(m, c.`1, c.`2);
      BadH.bad <- false;
      BadH.secret <- m;
      b' <@ A(BadH, L, K).guess(pk, c, k);
      return b';
  }}.

(* Game1.5: remove c1 from L *)
module Game1_5 = { proc main() : bool = {
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

module Game1_5h = { proc main() : bool = {
  var pk, m, e0, e1, lmask, c, k, b';
  H2.init(); L.init(); K.init();
  pk <$ distribution_over_R;
  m <$ duniformM;
    (e0, e1) <$ distribution_over_E_t;
      lmask <$ duniformM;
      c <- (e0 +e1 * pk, m + lmask);
      k <@ K.hash(m, c.`1, c.`2);
      BadH.bad <- false;
      BadH.secret <- m;
      b' <@ A(BadH, L, K).guess(pk, c, k);
      return b';
  }}.

module Game2b = { proc main() : bool = {
  var pk, m, lmask, c0, c, k, b';
  H2.init(); L.init(); K.init();
  pk <$ distribution_over_R;
  m <$ duniformM;
  lmask <$ duniformM;
  c0 <$ distribution_over_R;
  c <- (c0, m + lmask);
  k <@ K.hash(m, c.`1, c.`2);
  BadK.bad <- false;
  BadK.secret <- (m, c.`1, c.`2);
  b' <@ A(H2, L, BadK).guess(pk, c, k);
  return b';
  }}.

  (* Game2: c0 を一様化                                              *)
  module Game2 = { proc main() : bool = {
    var pk, m, lmask, c0, c, k, b';
    H2.init(); L.init(); K.init();
    pk <$ distribution_over_R;
    m <$ duniformM;
    lmask <$ duniformM;
    c0 <$ distribution_over_R;
    c <- (c0, m + lmask);
    k <@ K.hash(m, c.`1, c.`2);
    b' <@ A(H2, L, K).guess(pk, c, k);
    return b';
    }}.
  
  module Game3b = { proc main() : bool = {
    var pk, m, lmask, c0, c, k, b';
    H2.init(); L.init(); K.init();
    pk <$ distribution_over_R;
    m <$ duniformM;
    lmask <$ duniformM;
    c0 <$ distribution_over_R;
    c <- (c0, m + lmask);
    k <$ duniformK;
    BadK.bad <- false;
    BadK.secret <- (m, c.`1, c.`2);
    b' <@ A(H2, L, BadK).guess(pk, c, k);
    return b';
    }}.
  
  (* Game3: K_0 を一様化  [G2<->G3 : ROM bad-event] *)
  module Game3 = { proc main() : bool = {
    var pk, m, lmask, c0, c, k, b';
    H2.init(); L.init(); K.init();
    pk <$ distribution_over_R;
    m <$ duniformM;
    lmask <$ duniformM;
    c0 <$ distribution_over_R;
    c <- (c0, m + lmask);
    k <$ duniformK;
    b' <@ A(H2, L, K).guess(pk, c, k);
    return b';
    }}.

        (* Game3.5: c0 construction *)
  module Game3_5 = { proc main() : bool = {
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

lemma G1_5_eq &m :
    Pr[Game1_5.main() @ &m : res] = Pr[DQCSD(Red_sd(A)).main(false) @ &m : res].
    proof.
    byequiv => //.
      proc.
      inline DQCSD(Red_sd(A)).main Red_sd(A).distinguish H2.init L.init K.init
         ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
      swap{1} 5 1.
      sim.
      wp.
      rnd.
      rnd.
      wp.
      rnd{2}.
      wp.
      rnd.
      rnd.
    auto => />.
  qed.
  
lemma G2_eq &m :
    Pr[Game2.main() @ &m : res] = Pr[DQCSD(Red_sd(A)).main(true) @ &m : res].
    proof.
    byequiv => //.
    proc.
      inline DQCSD(Red_sd(A)).main Red_sd(A).distinguish H2.init L.init K.init
         ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
      sim.
      swap{1} 7 -2.
      rnd.
      rnd.
      wp.
      rnd.
      wp.
      rnd{2}.
      rnd.
    auto => />.
  qed.

lemma G3_eq &m :
    Pr[Game3.main() @ &m : res] = Pr[DQCSD(Red_sd_rand(A)).main(true) @ &m : res].
    proof.
    byequiv => //.
      proc.
      inline DQCSD(Red_sd_rand(A)).main Red_sd_rand(A).distinguish H2.init L.init K.init
         ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
      sim.
      swap{1} 7 -2.
      rnd.
      rnd.
      wp.
      rnd.
      wp.
      rnd{2}.
      rnd.
    auto => />.
  qed.

lemma G3_5_eq &m :
    Pr[Game3_5.main() @ &m : res] = Pr[DQCSD(Red_sd_rand(A)).main(false) @ &m : res].
    proof.
    byequiv => //.
      proc.
      inline DQCSD(Red_sd_rand(A)).main Red_sd_rand(A).distinguish H2.init L.init K.init
         ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
      sim.
      wp.
      rnd.
      swap{1} 5 1.
      rnd.
      wp.
      rnd{2}.
      wp.
      rnd.
      rnd.
    auto => />.
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

  lemma G1_G1b &m : Pr[Game1.main() @ &m : res] = Pr[Game1b.main() @ &m : res].
      proof.
      byequiv => //.
        proc.
        call(_: ={glob ROH.Lazy.LRO, glob ROL.Lazy.LRO, glob ROK.Lazy.LRO}).
        + by proc; sim.
        + proc; inline L.hash ROL.Lazy.LRO.o.
        seq 0 1 : (={x} /\ ={glob ROH.Lazy.LRO, glob ROL.Lazy.LRO, glob ROK.Lazy.LRO}).
        + by if{2}; auto.
        by sp; auto => />.
        + by proc; sim.
        wp.
        conseq (_: _ ==> ={pk, c, k, glob A, ROH.Lazy.LRO.m, ROL.Lazy.LRO.m, ROK.Lazy.LRO.m}) => />.
        sim; auto => />.
    qed.

  lemma G1_25_G1_25b &m : Pr[Game1_25.main() @ &m : res] = Pr[Game1_25b.main() @ &m : res].
      proof.
      byequiv => //.
        proc.
        call(_: ={glob ROH.Lazy.LRO, glob ROL.Lazy.LRO, glob ROK.Lazy.LRO}).
        + by proc; sim.
        + proc; inline L.hash ROL.Lazy.LRO.o.
        seq 0 1 : (={x} /\ ={glob ROH.Lazy.LRO, glob ROL.Lazy.LRO, glob ROK.Lazy.LRO}).
        + by if{2}; auto.
        by sp; auto => />.
        + by proc; sim.
        wp.
        conseq (_: _ ==> ={pk, c, k, glob A, ROH.Lazy.LRO.m, ROL.Lazy.LRO.m, ROK.Lazy.LRO.m}) => />.
        sim.
    qed.

  lemma G1_25_G1_25h &m : Pr[Game1_25.main() @ &m : res] = Pr[Game1_25h.main() @ &m :res].
      proof.
      byequiv => //.
        proc.
        call(_: ={glob ROH.Lazy.LRO, glob ROL.Lazy.LRO, glob ROK.Lazy.LRO}).
        + proc; inline H2.hash ROH.Lazy.LRO.o.
        seq 0 1 : (={x} /\ ={glob ROH.Lazy.LRO, glob ROL.Lazy.LRO, glob ROK.Lazy.LRO}).
        + by if{2}; auto.
        by sp; auto => />.
        + by proc; sim.
        + by proc; sim.
        wp.
        conseq (_: _ ==> ={pk, c, k, glob A, ROH.Lazy.LRO.m, ROL.Lazy.LRO.m, ROK.Lazy.LRO.m}) => />.
        sim.
    qed.

  lemma G1b_G1_25b_upto :
  equiv[Game1b.main ~ Game1_25b.main :
        ={glob A} ==> !BadL.bad{2} => ={res}].
      proof.
        proc.
        call (_: BadL.bad, ={ROH.Lazy.LRO.m, ROK.Lazy.LRO.m, BadL.secret} /\ FMap.eq_except (pred1 BadL.secret{2}) ROL.Lazy.LRO.m{1} ROL.Lazy.LRO.m{2}).
        exact A_guess_ll.
        proc; inline ROH.Lazy.LRO.o; auto => />.
      move=> *; proc; inline ROH.Lazy.LRO.o; auto => />; smt(DEt_ll).
      move=> *; proc; inline ROH.Lazy.LRO.o; auto => />; smt(DEt_ll).
        proc; inline L.hash ROL.Lazy.LRO.o.
        if; 1: by auto.
        wp; rnd; auto => />; smt().
        wp; rnd; auto => />; smt(FMap.get_setE FMap.get_set_neqE FMap.eq_except_set_eq FMap.eq_exceptP FMap.domNE).
      move=> *; proc; call L_hash_ll; auto.
      move=> *; proc; call L_hash_ll; auto.
        proc; inline ROK.Lazy.LRO.o; auto => />.
      move=> *; proc; inline ROK.Lazy.LRO.o; auto => />; smt(duniformM_ll).
      move=> *; proc; inline ROK.Lazy.LRO.o; auto => />; smt(duniformM_ll).
        wp.
        call K_hash_eq.
        wp.
        inline{1} L.hash ROL.Lazy.LRO.o.
        rcondt{1} 10.
      by move=> &m; inline *; auto => />; smt(FMap.mem_empty).
        wp; rnd.
        wp.
        call H2_hash_eq.
        inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
        wp; rnd; rnd.
      auto => />.
        smt(FMap.eq_except_setl FMap.get_set_sameE).
    qed.

  lemma G1b_G1_25b &m :
      `| Pr[Game1b.main() @ &m : res] - Pr[Game1_25b.main() @ &m : res] | <= Pr[Game1_25b.main() @ &m : BadL.bad].
      proof.
        have d1 : Pr[Game1b.main() @ &m : res] <= Pr[Game1_25b.main() @ &m : res \/ !BadL.bad].
      byequiv => //.
        conseq G1b_G1_25b_upto.
        smt().
        have d2 : Pr[Game1_25b.main() @ &m : res /\ !BadL.bad] <= Pr[Game1b.main() @ &m : res].
      byequiv => //. symmetry. conseq G1b_G1_25b_upto; smt().
        have or3 : Pr[Game1_25b.main() @ &m : res \/ BadL.bad] <= Pr[Game1_25b.main() @ &m : res] + Pr[Game1_25b.main() @ &m : BadL.bad].
        rewrite Pr[mu_or]; smt(mu_bounded).
        have sp3 : Pr[Game1_25b.main() @ &m : res \/ BadL.bad] = Pr[Game1_25b.main() @ &m : res] + Pr[Game1_25b.main() @ &m: BadL.bad].
        rewrite Pr[mu_split BadL.bad].
        smt().
        have b3 : Pr[Game1_25b.main() @ &m : res /\ BadL.bad] <= Pr[Game1_25b.main() @ &m : BadL.bad].
        rewrite Pr[mu_sub] //.
        smt().
    qed.
    
  lemma G1_5_G1_5h &m : Pr[Game1_5.main() @ &m : res] = Pr[Game1_5h.main() @ &m : res].
      proof.
      byequiv => //.
        proc.
        call(_: ={glob ROH.Lazy.LRO, glob ROL.Lazy.LRO, glob ROK.Lazy.LRO}).
        + proc; inline H2.hash ROH.Lazy.LRO.o.
        seq 0 1 : (={x} /\ ={glob ROH.Lazy.LRO, glob ROL.Lazy.LRO, glob ROK.Lazy.LRO}).
        + by if{2}; auto.
        by sp; auto => />.
        + by proc; sim.
        + by proc; sim.
        wp.
        conseq (_: _ ==> ={pk, c, k, glob A, ROH.Lazy.LRO.m, ROL.Lazy.LRO.m, ROK.Lazy.LRO.m}) => />.
        sim.
    qed.

  lemma G1_25h_G1_5h_upto :
  equiv[Game1_25h.main ~ Game1_5h.main :
        ={glob A} ==> !BadH.bad{2} => ={res}].
        proof.
          proc.
          call (_: BadH.bad, ={ROL.Lazy.LRO.m, ROK.Lazy.LRO.m, BadH.secret} /\ FMap.eq_except (pred1 BadH.secret{2}) ROH.Lazy.LRO.m{1} ROH.Lazy.LRO.m{2}).
          exact A_guess_ll.
          proc; inline H2.hash ROH.Lazy.LRO.o.
          if; 1: by auto.
          wp; rnd; auto => />; smt().
          wp; rnd; auto => />; smt(FMap.get_setE FMap.get_set_neqE FMap.eq_except_set_eq FMap.eq_exceptP FMap.domNE).
        move=> *; proc; call H2_hash_ll; auto.
        move=> *; proc; call H2_hash_ll; auto.
        proc; inline ROL.Lazy.LRO.o; auto => />.
        move=> *; proc; inline ROL.Lazy.LRO.o; auto => />; smt(duniformM_ll).
        move=> *; proc; inline ROL.Lazy.LRO.o; auto => />; smt(duniformM_ll).
        proc; inline ROK.Lazy.LRO.o; auto => />.
        move=> *; proc; inline ROK.Lazy.LRO.o; auto => />; smt(duniformM_ll).
        move=> *; proc; inline ROK.Lazy.LRO.o; auto => />; smt(duniformM_ll).
          wp.
          call K_hash_eq.
          wp.
          rnd.
          inline{1} H2.hash ROH.Lazy.LRO.o.
          rcondt{1} 9.
        by move=> &m; inline *; auto => />; smt(FMap.mem_empty).
          wp; rnd.
          inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
          wp; rnd; rnd.
        auto => />.
          smt(FMap.eq_except_setl FMap.get_set_sameE).
      qed.
      
        
  lemma G1_G1_5 &m :
      `| Pr[Game1.main() @ &m : res] - Pr[Game1_5.main() @ &m : res] | <= eps_rom.
      proof. admit. qed.

  lemma G1_5_G2 &m :
      `| Pr[Game1_5.main() @ &m : res] - Pr[ Game2.main() @ &m : res] | <= eps_qcsd.
      proof. rewrite (G1_5_eq &m) (G2_eq &m); exact (qcsd_hard &m (Red_sd(A))). qed.
    
  lemma G1_G2 &m :
    `| Pr[Game1.main() @ &m : res] - Pr[Game2.main() @ &m : res] | <= eps_qcsd + eps_rom.
      proof.
        have h1 := G1_G1_5 &m.
        have h2 := G1_5_G2 &m.
        smt().
    qed.

  lemma G2_G2b &m :
      Pr[Game2.main() @ &m : res] = Pr[Game2b.main() @ &m : res].
      proof.
        byequiv.
        proc.
        call(_: = {glob ROH.Lazy.LRO, glob ROL.Lazy.LRO, glob ROK.Lazy.LRO}).
        + by proc; sim.
        + by proc; sim.
        + proc; inline K.hash ROK.Lazy.LRO.o.
        seq 0 1 : (={x} /\ = {glob ROH.Lazy.LRO, glob ROL.Lazy.LRO, glob ROK.Lazy.LRO}).
        + by if{2}; auto.
        by sp; auto => />.
        wp.      
        conseq (_: _ ==> ={pk, c, k, glob A, ROH.Lazy.LRO.m, ROL.Lazy.LRO.m, ROK.Lazy.LRO.m}) => />.
        sim.
        auto => />.
        smt().
    qed.

  lemma G3_G3b &m :
      Pr[Game3.main() @ &m : res] = Pr[Game3b.main() @ &m : res].
      proof.
      byequiv => //.
        proc.
        call(_: ={glob ROH.Lazy.LRO, glob ROL.Lazy.LRO, glob ROK.Lazy.LRO}).
        + by proc; sim.
        + by proc; sim.
        + proc; inline K.hash ROK.Lazy.LRO.o.
        seq 0 1 : (={x} /\ ={glob ROH.Lazy.LRO, glob ROL.Lazy.LRO, glob ROK.Lazy.LRO}).
        + by if{2}; auto.
        by sp; auto => />.
        wp.
        conseq (_: _ ==> ={pk, c, k, glob A, ROH.Lazy.LRO.m, ROL.Lazy.LRO.m, ROK.Lazy.LRO.m}) => />.
        sim.
    qed.

  lemma G2b_G3b_upto :
  equiv[Game2b.main ~ Game3b.main :
        ={glob A} ==> !BadK.bad{2} => ={res}].
      proof.
        proc.
        call (_: BadK.bad, ={ROH.Lazy.LRO.m, ROL.Lazy.LRO.m, BadK.secret} /\ FMap.eq_except (pred1 BadK.secret{2}) ROK.Lazy.LRO.m{1} ROK.Lazy.LRO.m{2}).
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
      by move=> &m; inline *; auto => />; smt(FMap.mem_empty).
        inline H2.init L.init K.init ROH.Lazy.LRO.init ROL.Lazy.LRO.init ROK.Lazy.LRO.init.
        wp.
        rnd.
        wp.
        rnd.
        rnd.
        rnd.
        rnd.
      auto => />.
        smt(FMap.eq_except_setl FMap.get_set_sameE).      
    qed.

  lemma G2b_G3b &m :
      `| Pr[Game2b.main() @ &m : res] - Pr[Game3b.main() @ &m : res] | <= Pr[Game3b.main() @ &m : BadK.bad].
      proof.
        have d1 : Pr[Game2b.main() @ &m : res] <= Pr[Game3b.main() @ &m : res \/ BadK.bad].
      byequiv => //.
        conseq G2b_G3b_upto; smt().

        have d2 : Pr[Game3b.main() @ &m : res /\ !BadK.bad] <= Pr[Game2b.main() @ &m : res].
      byequiv => //.
        symmetry.
        conseq G2b_G3b_upto; smt().

        have or3 : Pr[Game3b.main() @ &m : res \/ BadK.bad] <= Pr[Game3b.main() @ &m : res] + Pr[Game3b.main() @ &m : BadK.bad].
        rewrite Pr[mu_or]; smt(mu_bounded).

        have sp3 : Pr[Game3b.main() @ &m : res]
      = Pr[Game3b.main() @ &m : res /\ !BadK.bad] + Pr[Game3b.main() @ &m : res /\ BadK.bad].
        rewrite Pr[mu_split BadK.bad]; smt().

        have b3 : Pr[Game3b.main() @ &m : res /\ BadK.bad] <= Pr[Game3b.main() @ &m : BadK.bad].
        rewrite Pr[mu_sub] //.
      
        smt().
    qed.
    
  lemma G2_G3 &m :
    `| Pr[Game2.main() @ &m : res] - Pr[Game3.main() @ &m : res] | <= eps_rom.
      proof.
        rewrite (G2_G2b &m) (G3_G3b &m).
        have h := G2b_G3b &m.
        have hbad : Pr[Game3b.main() @ &m : BadK.bad] <= eps_rom.
        admit.
        smt().
    qed.

  lemma G3_G3_5 &m :
      `| Pr[Game3.main() @ &m : res] - Pr[Game3_5.main() @ &m : res] | <= eps_qcsd.
      proof. rewrite (G3_eq &m) (G3_5_eq &m).
        have H := qcsd_hard &m (Red_sd_rand(A)).
        smt().
    qed.

  lemma G3_5_G4 &m :
      `| Pr[Game3_5.main() @ &m : res] - Pr[Game4.main() @ &m : res] | <= eps_rom.
      proof. admit. qed.

  lemma G3_G4 &m :
    `| Pr[Game3.main() @ &m : res] - Pr[Game4.main() @ &m : res] | <= eps_qcsd + eps_rom.
      proof.
        have h1 := G3_G3_5 &m.
        have h2 := G3_5_G4 &m.
        smt().
    qed.

  lemma G4_G5 &m :
    `| Pr[Game4.main() @ &m : res] - Pr[Game5.main() @ &m : res] | <= eps_qccf.
      proof.
        rewrite (G4_eq &m) (G5_eq &m).
        have H := qccf_hard &m (Red_cf_rand(A)).
        smt().
    qed.

  (* 主定理: 三角不等式で合成(HQC の Theorem1 と同型) *)
  lemma BIKE_KEM_IND_CPA &m :
    `| Pr[Game0.main() @ &m : res] - Pr[Game5.main() @ &m : res] |
       <= 2%r*eps_qccf + 2%r*eps_qcsd + 3%r*eps_rom.
  proof.
    have h01 := G0_G1 &m. have h12 := G1_G2 &m. have h23 := G2_G3 &m.
    have h34 := G3_G4 &m. have h45 := G4_G5 &m.
    smt().
  qed.

end section Security.
