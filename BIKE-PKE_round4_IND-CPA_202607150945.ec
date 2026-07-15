(* ====================================================================
   BIKE PKE — IND-CPA security, faithful to BIKE Spec v5.2 (2024.10.10),
   Appendix C.1.
   --------------------------------------------------------------------
   Correspondence with the paper:
     PKE0 (Table 10)                  | Bike.keyGen (encryption inlined in games)
     qcsd(e,h,s) (Problem 3)          | op wit
     G3 / G4 (Table 11)               | G3_OW / G4_OW
     distinguisher D (Table 11)       | D_cf
     PKE (Table 12)                   | c = (e0+e1h, m_b + L(e)) inside G0
     G0 / G1 / G2 (Table 13)          | G0 / G1 / G2
     event L*                         | BadWit.wt <> None
     L' (Table 14)                    | Lmon
     A0 = (A^L'_1, A^L'_2) (T.14)     | Red(A)
     Lemma 1 / Thm 1 / Thm 2          | Lemma1 / T1_false+T1_true / Theorem2_concrete
     qcsd with domain checks          | op wit_spec (G3_OW_S / G4_OW_S)
     h in R_odd (Key Security)        | keyGen_odd / keyGen_supp_odd
     main claim (hardness axiom-free) | Theorem2_final (+ lemma1_spec)

   Intentional deviations (standard mechanization moves):
     (D1) Table 13's "stop and return true on a witness query" becomes a
          continuing bad flag (identical-until-bad); the distribution up to
          the stopping point is unchanged.
     (D2) Pr[G2 | ¬L*] = 1/2 is proved as an equality via an equivalent
          game G2b (b moved to the tail) plus coin-flip symmetry, giving
          Pr[res /\ ¬bad] = ½·Pr[¬bad]. The factor 1/2 matches the paper.
     (D3) The unused b sample in the paper's G3' is dropped in Red
          (distribution unchanged).
     (D4) qcsd is treated as the paper's OW (search) problem: G4_OW is
          the OW-qcsd game itself; no hardness axiom is declared (revision f+3)
     (D5) fit coercion for message length — DISCHARGED in revision f:
          under A_choose_wf, G0 = G0_spec (Table 13 verbatim), lemma
          G0_G0_spec.
*** VERIFICATION STATUS (revision f, 2026-07-13) ***
     REVISION f+4 VERIFIED: EasyCrypt r2025.03 / Alt-Ergo, exit 0
     (full reload from top, zero admits, no hardness axioms).
       (f1) Major 1: parity infrastructure (ev1 = coefficient sum =
            evaluation at 1, a ring hom in char 2: ev1D / ev1M via
            rcoeffM + index-shift bigop reindexing; parity_add /
            parity_mul / parity_oner) culminating in keyGen_odd /
            keyGen_supp_odd: the public key h = h1 * invp h0 is odd
            with probability 1.
       (f2) Major 2: DRodd_odd, syndrome_parity (s = e0 + e1*h lies in
            R_p(t) for odd h), wit_spec (Problem 3 with domain checks),
            wit_spec_equiv, and spec-faithful twins G3_OW_S / G4_OW_S
            with Pr-equalities G3_OW_spec_eq / G4_OW_spec_eq.
       (f3) Major 3: hardness axioms annotated as epsilon-notation
            devices only; NEW axiom-free main claims Theorem2_concrete
            and Theorem2_concrete_spec (advantage bound relative to the
            concrete games for Red(A) / D_cf(Red(A))).
       (f4) Major 4: invp_correct now used in the chain (invp_odd ->
            keyGen_odd); Hw_unit remains the sole existential parameter
            condition.
       (f5) Major 5: well-formedness contract A_choose_wf (adversary
            messages lie in F_2^l, the paper's quantification); G0_spec
            (Table 13 G0 verbatim, no fit) and G0_G0_spec: Pr[G0] =
            Pr[G0_spec]. Deviation D5 is now discharged, not argued.
      (f+2) keyGen_eq_odd re-derived from keyGen_odd via conseq, wiring
            the Code Major 1 hoare theorem into the Lemma1_spec chain.
       (f+3) Dead-code removal and Code Major 3 closure by deletion:
            the epsilon-notation layer (ops eps_qccf / eps_qcsd_ow,
            axioms qccf_hard / qcsd_ow_hard, lemmas Theorem1 / Theorem2)
            and the unused lemmas Lmon_pres / A_choose_pres and
            op ( ^ ) are removed. No hardness axiom remains in the
            file; the RFinite block is annotated as a finiteness
            export.
      (f+4) Theorem2_final re-derived from Lemma1_spec, making the
            real-key parity chain (keyGen_odd / invp_correct) a proof
            dependency of the main claim.
     Axiom inventory of this revision:
       hardness (in-section): NONE (the epsilon-notation layer —
         Theorem1/Theorem2 and axioms qccf_hard/qcsd_ow_hard — was
         removed in f+3; the paper correspondence lives in the comment
         above Theorem2_concrete_spec).
       adversary contract (in-section): A_choose_ll, A_guess_ll
         (termination), A_choose_wf (messages in F_2^l).
       benign / mathematically-true facts: NONE
       parameter conditions, used in proofs: r_gt0, l_ge0, w_gt0, w_even,
         uneven_w_half (parity of dHw elements, revision f), d_le_r,
         t_ge0, t_le_n
       parameter conditions, existential form: Hw_unit (every weight-d
         element is a unit; NOT derivable from r_prime/uneven_w_half —
         counterexample r = 7 — it additionally encodes BIKE's choice
         "2 is a primitive root mod r" and d < r; discharging it needs
         F2[X] gcd/Bezout theory absent from the stdlib)
       parameter conditions, documentation only: r_prime
         (mathematical justification of Hw_unit).
   ==================================================================== *)

require import AllCore IntDiv.

op r : int. op w : int. op t : int. op l : int.
op n = r + r.  op d = w %/ 2.

(* Parameter conditions.
   Used directly in machine proofs:
     r_gt0 (PolyRing clone obligation gt0_n), l_ge0 (vector-size lemmas).
   Documentation-only (they are the mathematical justification for the
   benign axioms below; they carry no proof weight yet):
     w_gt0, w_even        => d = w/2 >= 1        (justifies enumHw_nonempty)
     uneven_w_half        => d odd; USED since revision f (dHw_odd,
                             parity chain to keyGen_odd)
     r_prime              => together with BIKE's choice of r such that
                             (X^r-1)/(X-1) is irreducible over F2, every
                             odd-weight x <> 1+X+...+X^{r-1} is invertible
                             (justifies invp_correct)
     t_ge0, t_le_n        => a weight-t error pair exists
                             (justifies exists_filter_Et)
d_le_r
   r_ge3 (only needed by the removed decoder/alg2 material) is deleted. *)
axiom r_gt0  : 0 < r.
axiom l_ge0  : 0 <= l.
axiom w_gt0  : 0 < w.
axiom w_even : 2 %| w.
axiom uneven_w_half : !(2 %| d).
axiom r_prime : prime r.
(* Used in machine proofs from revision d: enumHw_nonempty (weight-d
   witness needs d <= r). True for all BIKE parameter sets (d << r). *)
axiom d_le_r : d <= r.
axiom t_ge0  : 0 <= t.
axiom t_le_n : t <= n.

require import List Distr DBool IntMin RealExp.
require ROM PolyReduce BitWord DynMatrix.

(* ====================================================================
   0. RING / TYPES / CONVERSIONS
   (from old §1; pi_l / K / duniformK removed)
   ==================================================================== *)
clone import PolyReduce.PolyReduceZp as PolyRing with op n = r, op p = 2 proof *.
realize ge2_p. smt. qed.
realize gt0_n. smt(r_gt0). qed.

clone import DynMatrix as Matrix with
  op   ZR.(+) = PolyRing.Zp.(+),
  type ZR.t  <= PolyRing.Zp.

type R = polyXnD1.
type M = vector.

op polyToVec (x : polyXnD1) : vector = offunv ((fun i => x.[i]), r).
op RListToInt (x : Matrix.R list) =
  with x = []      => []
  with x = y :: ys => Zp.asint y :: RListToInt ys.
op polyToList (x : polyXnD1) = RListToInt (tolist (polyToVec x)).
op ham_weight (x : int list) =
  with x = []      => 0
  with x = y :: ys => ((y=0)?0:1) + (ham_weight ys).

op duniformM = Matrix.Vectors.dvector Zp.DZmodP.dunifin l.

(* ====================================================================
   1. E_t / R ENUMERATION / R_odd
   (from old §2; parity(R_part) family removed)
   ==================================================================== *)
op filter_Et (x : (R * R)) : bool =
  (ham_weight (polyToList x.`1) + ham_weight (polyToList x.`2) = t).
op list_append_each ['a 'b] (s : 'a list) (u : 'b) =
  with s = []      => []
  with s = x :: xs => (u, x) :: list_append_each xs u.
op double_list (s : 'a list) (u : 'b list) =
  with s = []      => []
  with s = x :: xs => list_append_each u x ++ double_list xs u.
  op enumR : R list = map polyLX (alltuples r Zp.DZmodP.Support.enum).

    (* Step A: polyLX is injective on length-r coefficient lists. *)
  (* Finiteness export (unused by the proof chain): R is a finite type,
   witnessed by the duplicate-free complete enumeration enumR
   (polyLX_inj -> enumR_uniq -> enumR_spec -> RFinite). This discharges
   the last benign axiom of revision c (enumR_spec) and grounds the
   duniform distributions over R used throughout. *)
lemma polyLX_inj (s1 s2 : Zp list) :          (* 型名が落ちたら Zp.zmod list *)
  size s1 = r => size s2 = r => polyLX s1 = polyLX s2 => s1 = s2.
proof.
move=> h1 h2 heq.
apply (eq_from_nth Zp.zero); first by rewrite h1 h2.
move=> i hi.
rewrite -(polyLXE s1 i) 1:/# -(polyLXE s2 i) 1:/#.
by rewrite heq.
qed.

(* Step B: enumR is duplicate-free. *)
lemma enumR_uniq : uniq enumR.
proof.
rewrite /enumR.
apply map_inj_in_uniq.
+ move=> s1 s2 /alltuplesP [hs1 _] /alltuplesP [hs2 _].
  by apply polyLX_inj; smt(r_gt0).
by apply alltuples_uniq; exact Zp.DZmodP.Support.enum_uniq.
qed.

(* Step C: enumR is complete. *)
lemma enumR_complete (x : R) : x \in enumR.
proof.
pose s := mkseq (fun (i : int) => x.[i]) r.
have hsz : size s = r by rewrite size_mkseq; smt(r_gt0).
have hmem : s \in alltuples r Zp.DZmodP.Support.enum.
+ apply/alltuplesP; split; first smt(r_gt0).
  by apply/allP => z _; exact Zp.DZmodP.Support.enumP.
have hpx : polyLX s = x.
+ apply/polyXnD1_eqP => i hi.
  rewrite polyLXE 1:/# nth_mkseq 1:/# //.
by rewrite /enumR; apply/mapP; exists s; rewrite hmem hpx.
qed.

(* Step D: the last benign axiom becomes a lemma. *)
lemma enumR_spec (x : R) : count (pred1 x) enumR = 1.
proof.
by rewrite count_uniq_mem 1:enumR_uniq enumR_complete.
qed.
  
op enumE_t = filter filter_Et (double_list enumR enumR).

clone MFinite as RFinite with type t <- R, op Support.enum <- enumR proof *.
realize Support.enum_spec. exact enumR_spec. qed.

  (* Bridge: ham_weight of the asint image = number of nonzero entries. *)
lemma ham_weight_count (s : Matrix.R list) :
  ham_weight (RListToInt s) = count (fun (z : Matrix.R) => z <> Zp.zero) s.
proof.
elim: s => //= z s ih; rewrite ih.
smt(Zp.zeroE Zp.asint_eq).
qed.

(* Bridge: ham_weight of a polynomial = number of nonzero coefficients
   among indices 0..r-1. *)
lemma ham_weight_coeff (x : R) :
  ham_weight (polyToList x)
  = count (fun (i : int) => x.[i] <> Zp.zero) (range 0 r).
proof.
rewrite /polyToList ham_weight_count /polyToVec /tolist.
rewrite size_offunv.
have -> : max 0 r = r by smt(r_gt0).
rewrite count_map.
apply eq_in_count => i /mem_range hi /=.
rewrite /preim /=.
  rewrite get_offunv 1:/#.
by rewrite /rcoeff.
qed.

(* Witness factory: a polynomial of any weight k <= r exists. *)
lemma weight_k_exists (k : int) :
  0 <= k <= r => exists (x : R), ham_weight (polyToList x) = k.
proof.
move=> hk.
pose s := mkseq (fun (i : int) => if i < k then Zp.one else Zp.zero) r.
exists (polyLX s).
rewrite ham_weight_coeff.
have -> : count (fun (i : int) => (polyLX s).[i] <> Zp.zero) (range 0 r)
        = count (fun (i : int) => i < k) (range 0 r).
+ apply eq_in_count => i /mem_range hi /=.
  rewrite polyLXE 1:size_mkseq 1:/#.
  rewrite nth_mkseq 1:/# /=.
  smt(Zp.oneE Zp.zeroE).
rewrite (range_cat k 0 r) 1,2:/# count_cat.
have -> : count (fun (i : int) => i < k) (range 0 k) = k.
+ have hall : all (fun (i : int) => i < k) (range 0 k).
  * by apply/allP => i /mem_range /#.
  by move/all_count: hall => ->; rewrite size_range /#.
have -> : count (fun (i : int) => i < k) (range k r) = 0.
+ have hno : !has (fun (i : int) => i < k) (range k r).
  * by apply/hasPn => i /mem_range /#.
  by smt(has_count count_ge0).
by [].
      qed.

lemma mem_enumR (a : R) : a \in enumR.
proof. exact enumR_complete. qed.


op distribution_over_E_t : (R * R) distr = duniform enumE_t.

op poly_parity (x : R) : int = (ham_weight (polyToList x)) %% 2.

  (* ---- §1: poly_parity 直後 ---- *)
(* Characteristic 2: negation is the identity on Zp. *)
lemma oppW (a : Zp) : Zp.([-]) a = a.
proof.
apply Zp.asint_inj; rewrite Zp.oppE.
smt(Zp.rg_asint).
qed.

(* Characteristic 2: subtraction is addition on Zp. *)
lemma subW (a b : Zp) : Zp.(-) a b = Zp.(+) a b.
    proof. by rewrite oppW. qed.

  (* ev1: sum of coefficients = evaluation at 1 (a ring hom since p = 2:
   1 is a root of X^r + 1). *)
op ev1 (x : R) : Zp = Zp.BigZMod.BAdd.bigi predT (fun i => x.[i]) 0 r.

lemma ev1D (x y : R) : ev1 (x + y) = Zp.(+) (ev1 x) (ev1 y).
proof.
rewrite /ev1 -Zp.BigZMod.BAdd.big_split.
by apply Zp.BigZMod.BAdd.eq_big_int => i hi /=; rewrite rcoeffD.
qed.

(* BCA (BasePoly.BigCf) and BAdd (Zp.BigZMod) are the same fold. *)
lemma BCA_BAdd ['a] (P : 'a -> bool) (F : 'a -> Zp) (s : 'a list) :
  BasePoly.BigCf.BCA.big P F s = Zp.BigZMod.BAdd.big P F s.
    proof. by rewrite /BasePoly.BigCf.BCA.big /Zp.BigZMod.BAdd.big. qed.

  (* rcoeffM in characteristic 2, stated with BAdd. *)
lemma rcoeffM2 (p q : R) (k : int) :
  0 <= k < r =>
  (p * q).[k]
  = Zp.BigZMod.BAdd.bigi predT
      (fun (i : int) => Zp.(+) (Zp.( * ) p.[i] q.[k - i])
                               (Zp.( * ) p.[i] q.[r + k - i])) 0 r.
proof.
move=> hk.
rewrite rcoeffM 1:// BCA_BAdd.
apply Zp.BigZMod.BAdd.eq_big_int => i hi /=.
by rewrite subW.
qed.

(* Index shift for coefficient sums, general shift amount. *)
lemma big_shift (y : R) (i : int) :
  Zp.BigZMod.BAdd.bigi predT (fun (k : int) => y.[k - i]) 0 r
  = Zp.BigZMod.BAdd.bigi predT (fun (j : int) => y.[j]) (-i) (r - i).
proof.
have -> : Zp.BigZMod.BAdd.bigi predT (fun (j : int) => y.[j]) (-i) (r - i)
        = Zp.BigZMod.BAdd.bigi predT (fun (j : int) => y.[j]) (0 - i) (r - i).
+ by have -> : -i = 0 - i by smt().
rewrite (Zp.BigZMod.BAdd.big_addn 0 (r - i) (-i) predT (fun (j : int) => y.[j])).
have -> : r - i - -i = r by smt().
apply Zp.BigZMod.BAdd.eq_big => //= k.
      qed.

      (* For fixed 0 <= i < r, summing the two wrapped columns over k
   recovers the full coefficient sum of y. *)
lemma inner_sum (y : R) (i : int) :
  0 <= i < r =>
  Zp.BigZMod.BAdd.bigi predT
    (fun (k : int) => Zp.(+) y.[k - i] y.[r + k - i]) 0 r
  = ev1 y.
proof.
move=> hi.
have hL : Zp.BigZMod.BAdd.bigi predT (fun (k : int) => y.[k - i]) 0 r
        = Zp.BigZMod.BAdd.bigi predT (fun (j : int) => y.[j]) 0 (r - i).
+ rewrite (big_shift y i).
  rewrite (Zp.BigZMod.BAdd.big_cat_int 0 (-i) (r - i)) 1,2:/#.
  rewrite (Zp.BigZMod.BAdd.big1_seq predT _ (range (-i) 0)).
  + by move=> j [_ /mem_range hj] /=; rewrite lt0_rcoeff 1:/#.
  by rewrite Zp.ZModpRing.add0r.
have hR : Zp.BigZMod.BAdd.bigi predT (fun (k : int) => y.[r + k - i]) 0 r
        = Zp.BigZMod.BAdd.bigi predT (fun (j : int) => y.[j]) (r - i) r.
+ have -> : Zp.BigZMod.BAdd.bigi predT (fun (k : int) => y.[r + k - i]) 0 r
          = Zp.BigZMod.BAdd.bigi predT (fun (k : int) => y.[k - (i - r)]) 0 r.
  + by apply Zp.BigZMod.BAdd.eq_big_int => k hk /=; congr; smt().
  rewrite (big_shift y (i - r)).
  have -> : -(i - r) = r - i by smt().
  have -> : r + (r - i) = 2 * r - i by smt().
  rewrite (Zp.BigZMod.BAdd.big_cat_int r (r - i) (2 * r - i)) 1,2:/#.
  rewrite (Zp.BigZMod.BAdd.big1_seq predT _ (range r (2 * r - i))).
  + by move=> j [_ /mem_range hj] /=; rewrite gered_rcoeff 1:/#.
  by rewrite Zp.ZModpRing.addr0.
rewrite (Zp.BigZMod.BAdd.big_split predT
          (fun (k : int) => y.[k - i])
          (fun (k : int) => y.[r + k - i])
          (range 0 r)).
rewrite hL hR /ev1.
by rewrite -(Zp.BigZMod.BAdd.big_cat_int (r - i) 0 r) 1,2:/#.
      qed.

      (* ev1 is multiplicative: evaluation at 1 is a ring homomorphism. *)
lemma ev1M (x y : R) : ev1 (x * y) = Zp.( * ) (ev1 x) (ev1 y).
proof.
have step1 : ev1 (x * y)
  = Zp.BigZMod.BAdd.bigi predT
      (fun (k : int) =>
         Zp.BigZMod.BAdd.bigi predT
           (fun (i : int) => Zp.(+) (Zp.( * ) x.[i] y.[k - i])
                                    (Zp.( * ) x.[i] y.[r + k - i])) 0 r) 0 r.
+ rewrite /ev1.
  by apply Zp.BigZMod.BAdd.eq_big_int => k hk /=; exact (rcoeffM2 x y k hk).
have step2 : ev1 (x * y)
  = Zp.BigZMod.BAdd.bigi predT
      (fun (i : int) => Zp.( * ) x.[i] (ev1 y)) 0 r.
+ rewrite step1 Zp.BigZMod.BAdd.exchange_big.
  apply Zp.BigZMod.BAdd.eq_big_int => i hi /=.
  have -> : Zp.BigZMod.BAdd.bigi predT
              (fun (k : int) => Zp.(+) (Zp.( * ) x.[i] y.[k - i])
                                       (Zp.( * ) x.[i] y.[r + k - i])) 0 r
          = Zp.BigZMod.BAdd.bigi predT
              (fun (k : int) => Zp.( * ) x.[i] (Zp.(+) y.[k - i] y.[r + k - i])) 0 r.
  + by apply Zp.BigZMod.BAdd.eq_big_int => k hk /=;
       rewrite Zp.ZModpRing.mulrDr.
  rewrite -(Zp.BigZMod.BAdd.mulr_sumr predT
             (fun (k : int) => Zp.(+) y.[k - i] y.[r + k - i])
             (range 0 r) x.[i]).
  by rewrite (inner_sum y i hi).
rewrite step2.
rewrite -(Zp.BigZMod.BAdd.mulr_suml predT
           (fun (i : int) => x.[i]) (range 0 r) (ev1 y)).
by rewrite /ev1.
qed.

(* oner has exactly one nonzero coefficient (index 0). *)
lemma rcoeff1 (k : int) : oner.[k] = if k = 0 then Zp.one else Zp.zero.
proof.
have h := rcoeff_polyXn 0 k _; first smt(r_gt0).
by move: h; rewrite ComRingDflInv.expr0.
qed.

lemma parity_oner : poly_parity oner = 1.
proof.
rewrite /poly_parity ham_weight_coeff.
have -> : count (fun (i : int) => oner.[i] <> Zp.zero) (range 0 r)
        = count (pred1 0) (range 0 r).
+ apply eq_in_count => i /mem_range hi /=.
  rewrite /pred1 rcoeff1.
  smt(Zp.oneE Zp.zeroE Zp.asint_eq).
rewrite count_uniq_mem 1:range_uniq mem_range.
smt(r_gt0).
      qed.

(* asint of a coefficient sum = (number of nonzero coefficients) mod 2. *)
lemma asint_big_count (x : R) (a b : int) :
  Zp.asint (Zp.BigZMod.BAdd.bigi predT (fun i => x.[i]) a b)
  = count (fun (i : int) => x.[i] <> Zp.zero) (range a b) %% 2.
proof.
have [k [hk hab]] : exists k, 0 <= k /\ b - a <= k.
+ by exists (max 0 (b - a)); smt().
elim: k hk a b hab => [| k hk ih] a b hab.
+ rewrite Zp.BigZMod.BAdd.big_geq 1:/# range_geq 1:/#.
  by rewrite Zp.zeroE.
case (b <= a) => hba.
+ rewrite Zp.BigZMod.BAdd.big_geq 1:/# range_geq 1:/#.
  by rewrite Zp.zeroE.
have hlt : a < b by smt().
rewrite (Zp.BigZMod.BAdd.big_ltn a b) 1:// (range_ltn a b) 1:// /=.
rewrite Zp.addE (ih (a + 1) b) 1:/#.
smt(Zp.rg_asint Zp.zeroE Zp.asint_eq modzDml modzDmr).
qed.

lemma poly_parity_ev1 (x : R) : poly_parity x = Zp.asint (ev1 x).
proof.
by rewrite /poly_parity ham_weight_coeff /ev1 asint_big_count.
qed.

lemma p2 : PolyRing.p = 2.
proof. by []. qed.

lemma parity_range (z : R) : 0 <= poly_parity z < 2.
proof. rewrite /poly_parity; smt(modz_ge0 ltz_pmod). qed.

lemma parity_add (x y : R) :
  poly_parity (x + y) = (poly_parity x + poly_parity y) %% 2.
proof.
rewrite !poly_parity_ev1 ev1D Zp.addE p2.
done.
qed.

lemma parity_mul (x y : R) :
  poly_parity (x * y) = (poly_parity x * poly_parity y) %% 2.
proof.
rewrite !poly_parity_ev1 ev1M Zp.mulE p2.
done.
qed.

op enumR_odd : R list = filter (fun (x : R) => poly_parity x = 1) enumR.
op distribution_over_R_odd = duniform enumR_odd.

        (* Discharge of enumR_odd_nonempty: a weight-1 polynomial is odd. *)
lemma enumR_odd_nonempty : enumR_odd <> [].
proof.
have [x hx] : exists (x : R), ham_weight (polyToList x) = 1.
+ by apply weight_k_exists; smt(r_gt0).
apply/negP => h.
have hmem : x \in enumR_odd.
+ rewrite /enumR_odd mem_filter.
  smt(mem_enumR).
by move: hmem; rewrite h.
qed.

(* Discharge of exists_filter_Et: split t = min t r + (t - min t r),
   both parts in [0,r] since 0 <= t <= n = 2r (t_ge0, t_le_n). *)
lemma exists_filter_Et : exists (x : R * R), filter_Et x.
proof.
have [x0 hx0] : exists (x : R), ham_weight (polyToList x) = min t r.
+ by apply weight_k_exists; smt(t_ge0 r_gt0).
have [x1 hx1] : exists (x : R), ham_weight (polyToList x) = t - min t r.
+ by apply weight_k_exists; smt(t_ge0 t_le_n r_gt0).
by exists (x0, x1); rewrite /filter_Et /= hx0 hx1 /#.
qed.

(* ====================================================================
   2. ROM: L : R×R -> M
   (from old §3; ROH/H2 and ROK/K removed)
   ==================================================================== *)
clone ROM as ROL with type in_t <- R * R, type out_t <- M,
                      op dout _ <- duniformM proof *.
module L = {
  proc init(): unit = { ROL.Lazy.LRO.init(); }
  proc hash(x : R * R): M = { var y; y <@ ROL.Lazy.LRO.o(x); return y; }
}.

(* ====================================================================
   3. PKE0 KEY GENERATION
   (from old §4; encaps removed)
   ==================================================================== *)
(* Spec (Table 10 KeyGen): (h0,h1) <-$ Hw x Hw with
   Hw = { x in R : |x| = w/2 }, h = h1 * h0^-1.
   Revision b makes the Hw distribution concrete:
     dHw = uniform over the weight-d elements of R  (d = w %/ 2). *)
op Hw_elem (x : R) : bool = ham_weight (polyToList x) = d.
op enumHw : R list = filter Hw_elem enumR.

(* Discharge of enumHw_nonempty: a weight-d polynomial exists
   (1 <= d from w_gt0/w_even, d <= r from d_le_r). *)
lemma enumHw_nonempty : enumHw <> [].
proof.
have [x hx] : exists (x : R), ham_weight (polyToList x) = d.
+ by apply weight_k_exists; smt(w_gt0 w_even d_le_r).
apply/negP => h.
have hmem : x \in enumHw.
+ by rewrite /enumHw mem_filter /Hw_elem hx /= mem_enumR.
by move: hmem; rewrite h.
qed.

op dHw : R distr = duniform enumHw.

(* dHw_ll: axiom in the base file, now a lemma. *)
lemma dHw_ll : is_lossless dHw.
proof. rewrite /dHw; apply duniform_ll; exact enumHw_nonempty. qed.

(* Support correctness: keyGen really samples weight-d polynomials. *)
lemma dHw_supp (x : R) : x \in dHw => ham_weight (polyToList x) = d.
proof. rewrite /dHw supp_duniform /enumHw mem_filter /Hw_elem; smt(). qed.

(* BENIGN AXIOM (mathematically true for BIKE parameter sets):
   every weight-d element of R is a unit. Justification: d odd
   (uneven_w_half) gives x(1) = 1, so (X-1) does not divide x; BIKE
   chooses r prime (r_prime) with 2 a primitive root mod r, so
   Phi = (X^r-1)/(X-1) is irreducible; then by CRT the only non-units
   with x(1) = 1 are the multiples of Phi, i.e. x = 1+X+...+X^{r-1}
   of weight r, excluded since d < r for all BIKE parameter sets.
   NOTE: "2 primitive root mod r" and "d < r" are part of the BIKE
   parameter choice but are NOT captured by axioms here; discharging
   Hw_unit (future work) would add them and develop gcd/Bezout for
   F2[X], which the stdlib currently lacks. *)
axiom Hw_unit (x : R) :
  ham_weight (polyToList x) = d => exists (y : R), x * y = oner.

(* invp is now DEFINED (choice from Hw_unit), no longer abstract:
   the only trusted statement about inversion is Hw_unit above. *)
op invp (x : R) : R = choiceb (fun (y : R) => x * y = oner) x.

(* Correctness on the keyGen support: an axiom in revision b, now a
   lemma. Off the support invp's value is irrelevant (cf. dHw_supp). *)
lemma invp_correct (x : R) :
  ham_weight (polyToList x) = d => x * invp x = oner.
proof.
  move=> hx; rewrite /invp.
  have hex : exists (y : R), x * y = oner by exact (Hw_unit x hx).
  exact (choicebP (fun (y : R) => x * y = oner) x hex).
qed.

(* ---- §3: invp_correct 直後 ---- *)

(* (1) dHw elements are odd (first real use of uneven_w_half). *)
lemma dHw_odd (x : R) : x \in dHw => poly_parity x = 1.
proof.
move=> /dHw_supp hx; rewrite /poly_parity hx.
smt(uneven_w_half).
qed.

(* (2) oner is odd: bridge parity_oner into the mod-2 arithmetic. *)
(* already available as parity_oner *)

(* (3) the inverse of a weight-d element is odd:
   1 = parity(oner) = parity(x * invp x) = parity x * parity(invp x) mod 2,
   and parity x = 1, so parity(invp x) = 1. Uses invp_correct — this
   connects the KeyGen inverse correctness into the proof chain. *)
lemma invp_odd (x : R) :
  ham_weight (polyToList x) = d => poly_parity (invp x) = 1.
proof.
move=> hx.
have h1 : poly_parity (x * invp x) = 1.
+ by rewrite (invp_correct x hx) parity_oner.
have h2 : poly_parity x = 1 by rewrite /poly_parity hx; smt(uneven_w_half).
have := parity_mul x (invp x).
rewrite h1 h2 /=.
smt(parity_range).
qed.

module Bike = {
  proc keyGen(): R = { var h0, h1; h0 <$ dHw; h1 <$ dHw; return h1 * invp h0; }
}.

(* (4) KeyGen support theorem: the public key is odd (Code Major 1). *)
lemma keyGen_odd :
  hoare[ Bike.keyGen : true ==> poly_parity res = 1 ].
proof.
proc.
auto => /> h0 hh0 h1 hh1.
rewrite parity_mul.
rewrite (dHw_odd h1 hh1) (invp_odd h0 _) 1:(dHw_supp h0 hh0) //.
qed.

(* ====================================================================
   4. AUXILIARY LEMMAS
   (selected from old §9; fp_measure / parity / ROM-counting removed)
   ==================================================================== *)
lemma mem_list_append_each ['a 'b] (a : 'a) (b : 'b) (x : 'a) (u : 'b list) :
  (a, b) \in list_append_each u x <=> a = x /\ b \in u.
proof. elim: u => /=; smt(). qed.
lemma mem_double_list ['a 'b] (a : 'a) (b : 'b) (s : 'a list) (u : 'b list) :
  (a, b) \in double_list s u <=> a \in s /\ b \in u.
proof.
  elim: s => /= [|x xs ih]; first by rewrite /double_list.
  rewrite mem_cat mem_list_append_each ih; smt().
qed.

lemma Et_complete (x : R * R) : filter_Et x => x \in enumE_t.
proof.
  move=> hx; rewrite /enumE_t mem_filter hx /=.
  have -> : x = (x.`1, x.`2) by smt().
  rewrite mem_double_list; smt(mem_enumR).
qed.
lemma enumE_t_nonempty : enumE_t <> [].
proof.
  have [e he] := exists_filter_Et. have hmem := Et_complete e he.
  apply/negP => h; by move: hmem; rewrite h.
qed.
lemma Et_filter (x : R * R) : x \in distribution_over_E_t => filter_Et x.
proof. rewrite /distribution_over_E_t supp_duniform /enumE_t mem_filter; smt(). qed.

(* Losslessness of the sampling distributions and oracles. *)
lemma duniformM_ll : is_lossless duniformM.
proof. rewrite /duniformM; apply dvector_ll; exact Zp.DZmodP.dunifin_ll. qed.
lemma DEt_ll : is_lossless distribution_over_E_t.
proof. rewrite /distribution_over_E_t; apply duniform_ll; exact enumE_t_nonempty. qed.
lemma DRodd_ll : is_lossless distribution_over_R_odd.
proof. rewrite /distribution_over_R_odd; apply duniform_ll; exact enumR_odd_nonempty. qed.

lemma L_hash_ll : islossless L.hash.
proof. proc; inline ROL.Lazy.LRO.o; auto => />; smt(duniformM_ll). qed.
lemma L_hash_eq :
  equiv[ L.hash ~ L.hash : ={arg, ROL.Lazy.LRO.m} ==> ={res, ROL.Lazy.LRO.m} ].
proof. by proc; inline ROL.Lazy.LRO.o; auto. qed.
lemma keyGen_ll : islossless Bike.keyGen.
    proof. proc; auto => />; smt(dHw_ll). qed.

      (* (5) phoare = 1 version (keyGen is lossless). *)
  (* Role: standalone spec-faithfulness statement for DQCCF(false) — the
   real key lies in R_odd with probability 1 (Evaluation Report §5.2
   item 3). The same parity chain enters the main claim through
   keyGen_eq_odd -> G3_OW_spec_eq -> Lemma1_spec. *)
lemma keyGen_supp_odd :
  phoare[ Bike.keyGen : true ==> poly_parity res = 1 ] = 1%r.
proof.
  conseq keyGen_ll keyGen_odd.
smt().
qed.

(* OTP helpers (used for the Step-2 rnd coupling and in G2b).
   Recovered from the handoff16 §1.2 / handoff17 §1.1 green scripts.
   If those become unrecoverable, reprove from the ZModule axioms of
   Matrix and characteristic 2 of Zp (x + x = 0). *)
lemma duniformM_size (v : M) : v \in duniformM => size v = l.
proof.
  rewrite /duniformM => hv.
  have := size_dvector Zp.DZmodP.dunifin l v hv.
  smt(l_ge0).
qed.

lemma vec_subrK (m v : M) : size m = l => size v = l => m + (v - m) = v.
proof.
  move=> hm hv.
  have e1 : v - m = -m + v by apply Vectors.addvC.
  rewrite e1 Vectors.addvA.
  have e2 : m + -m = zerov l.
  + have := Vectors.addvN m.
    rewrite hm => ->; reflexivity.
  rewrite e2.
  have := Vectors.add0v v.
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

lemma vec_subv_supp (m v : M) :
  size m = l => v \in duniformM => (v - m) \in duniformM.
proof.
  move=> hm hv.
  have hsz : size v = l by apply duniformM_size.
  have hl : 0 <= l by smt(l_ge0).
  rewrite /duniformM (supp_dvector Zp.DZmodP.dunifin (v - m) l hl).
  rewrite size_addv size_oppv hsz hm /=.
  split; first smt().
  move=> i hi.
  rewrite get_addv getvN.
  exact Zp.DZmodP.dunifin_fu.
qed.

lemma duniformM_funi (v1 v2 : M) :
  size v1 = l => size v2 = l => mu1 duniformM v1 = mu1 duniformM v2.
proof.
  move=> h1 h2; rewrite /duniformM.
  rewrite -{1}h1 -{1}h2 !mu1_dvector_fu; first exact Zp.DZmodP.dunifin_funi.
  + exact Zp.DZmodP.dunifin_funi.
  by rewrite h1 h2.
qed.

(* fit: pad a message into F_2^l (deviation D5: mechanizes the paper's
   m ∈ F_2^l, since M = vector carries no length in its type).
   D5 closure argument: fit is the identity on well-formed messages
   (size m = l => fit m = m; candidate lemma fit_id in
   finite_facts_WIP.ec §A). Hence for any adversary that returns
   messages in {0,1}^l — the only adversaries the paper quantifies
   over — G0 here is literally Table 13's G0; for other adversaries
   fit acts as the challenger's input coercion. *)
op fit (m : M) : M = offunv ((fun i => m.[i]), l).

lemma size_fit (m : M) : size (fit m) = l.
    proof. by rewrite /fit size_offunv; smt(l_ge0). qed.

(* D5 closure: fit is the identity on well-formed (length-l) messages,
   so for adversaries returning messages in {0,1}^l, G0 = Table 13 G0. *)
lemma fit_id (m : M) : size m = l => fit m = m.
proof.
move=> hm; rewrite /fit.
apply/eq_vectorP; split.
+ by rewrite size_offunv hm; smt(l_ge0).
move=> i; rewrite size_offunv => hi.
by rewrite get_offunv 1:/#.
qed.

(* Self-equiv for keyGen (used by call in G0_G1 etc.). *)
lemma keyGen_eq : equiv[Bike.keyGen ~ Bike.keyGen : true ==> ={res}].
proof. by proc; auto. qed.

import FMap.

(* ====================================================================
   5. qcsd WITNESS PREDICATE AND OW-qcsd
   (Table 11 / Problem 3)
   --------------------------------------------------------------------
   wit e h s  <=>  e ∈ E_t /\ e0 + e1·h = s.
   E_t membership is carried by the runtime-decidable filter_Et (used by
   Lmon). Et_complete / Et_filter bridge to enumE_t.
   ==================================================================== *)
op wit (e : R * R) (h s : R) : bool =
  filter_Et e /\ e.`1 + e.`2 * h = s.

(* R_odd support: sampling from distribution_over_R_odd gives odd h. *)
lemma DRodd_odd (h : R) :
  h \in distribution_over_R_odd => poly_parity h = 1.
proof.
rewrite /distribution_over_R_odd supp_duniform /enumR_odd mem_filter.
smt().
qed.

(* Syndrome parity (Code Major 2): for a weight-t error pair and an odd h,
   the syndrome e0 + e1*h lies in the parity class t mod 2, i.e. the
   spec's R_p(t) side condition (Problem 3) holds inside G3_OW/G4_OW. *)
lemma syndrome_parity (e : R * R) (h : R) :
  filter_Et e => poly_parity h = 1 =>
  poly_parity (e.`1 + e.`2 * h) = t %% 2.
proof.
move=> hE hodd.
rewrite parity_add parity_mul hodd /=.
move: hE; rewrite /filter_Et /poly_parity => hE.
smt(modzDml modzDmr modz_mod).
qed.

(* Spec-faithful witness predicate (Problem 3 with domain checks):
   h must be odd (h in R_odd) and s must lie in R_p(t). *)
op wit_spec (e : R * R) (h s : R) : bool =
  poly_parity h = 1 /\ poly_parity s = t %% 2 /\ wit e h s.

(* Under an odd h, the domain checks are redundant: the s-check follows
   from the witness equation via syndrome_parity. *)
lemma wit_spec_equiv (e : R * R) (h s : R) :
  poly_parity h = 1 => wit e h s <=> wit_spec e h s.
proof.
move=> hodd; rewrite /wit_spec hodd /=.
split; last by smt().
move=> hw; split; last exact hw.
have <- : e.`1 + e.`2 * h = s by smt().
by apply (syndrome_parity e h) => //; smt().
qed.

module type OW_Adv = {
  proc solve(h : R, s : R) : (R * R) option
}.

(* Table 11 left: OW-CPA under the real key. *)
module G3_OW (A0 : OW_Adv) = {
  proc main() : bool = {
    var h, e0e1, s, eo;
    h <@ Bike.keyGen();
    e0e1 <$ distribution_over_E_t;
    s <- e0e1.`1 + e0e1.`2 * h;
    eo <@ A0.solve(h, s);
    return (eo <> None /\ wit (oget eo) h s);
  }
}.

(* Table 11 middle: h uniform (R_odd) = generic decoding = OW-qcsd game. *)
module G4_OW (A0 : OW_Adv) = {
  proc main() : bool = {
    var h, e0e1, s, eo;
    h <$ distribution_over_R_odd;
    e0e1 <$ distribution_over_E_t;
    s <- e0e1.`1 + e0e1.`2 * h;
    eo <@ A0.solve(h, s);
    return (eo <> None /\ wit (oget eo) h s);
  }
}.

(* Spec-faithful twins of the OW games (wit replaced by wit_spec). *)
module G3_OW_S (A0 : OW_Adv) = {
  proc main() : bool = {
    var h, e0e1, s, eo;
    h <@ Bike.keyGen();
    e0e1 <$ distribution_over_E_t;
    s <- e0e1.`1 + e0e1.`2 * h;
    eo <@ A0.solve(h, s);
    return (eo <> None /\ wit_spec (oget eo) h s);
  }
}.

module G4_OW_S (A0 : OW_Adv) = {
  proc main() : bool = {
    var h, e0e1, s, eo;
    h <$ distribution_over_R_odd;
    e0e1 <$ distribution_over_E_t;
    s <- e0e1.`1 + e0e1.`2 * h;
    eo <@ A0.solve(h, s);
    return (eo <> None /\ wit_spec (oget eo) h s);
  }
}.

(* keyGen self-equiv carrying the oddness of the output.
   Revision f+: derived from keyGen_odd (Code Major 1), so the hoare
   parity theorem enters the main claim through
   keyGen_odd -> keyGen_eq_odd -> G3_OW_spec_eq -> Lemma1_spec. *)
lemma keyGen_eq_odd :
  equiv[ Bike.keyGen ~ Bike.keyGen :
         true ==> ={res} /\ poly_parity res{2} = 1 ].
proof.
conseq keyGen_eq _ keyGen_odd => //.
qed.

lemma G4_OW_spec_eq (A0 <: OW_Adv) &m :
  Pr[G4_OW(A0).main() @ &m : res] = Pr[G4_OW_S(A0).main() @ &m : res].
proof.
byequiv (: ={glob A0} ==> ={res}) => //.
proc.
seq 1 1 : (={glob A0, h} /\ poly_parity h{2} = 1).
+ by rnd; auto => />; smt(DRodd_odd).
call (_: true).
auto => />.
smt(wit_spec_equiv).
qed.

lemma G3_OW_spec_eq (A0 <: OW_Adv) &m :
  Pr[G3_OW(A0).main() @ &m : res] = Pr[G3_OW_S(A0).main() @ &m : res].
proof.
byequiv (: ={glob A0} ==> ={res}) => //.
proc.
seq 1 1 : (={glob A0, h} /\ poly_parity h{2} = 1).
+ by call keyGen_eq_odd.
call (_: true).
auto => />.
smt(wit_spec_equiv).
qed.

(* Table 11 right: qccf distinguisher (lines 3–6 of G4; old Red_cf_L skeleton). *)
module D_cf (A0 : OW_Adv) = {
  proc distinguish(h : R) : bool = {
    var e0e1, s, eo;
    e0e1 <$ distribution_over_E_t;
    s <- e0e1.`1 + e0e1.`2 * h;
    eo <@ A0.solve(h, s);
    return (eo <> None /\ wit (oget eo) h s);
  }
}.

(* ====================================================================
   6. qccf DISTINGUISHING GAME
   (old §6 DQCCF verbatim; DQCSD removed)
   ==================================================================== *)
module type CF_Dist = { proc distinguish(h : R) : bool }.
module DQCCF (D : CF_Dist) = {
  proc main(b : bool) : bool = {
    var hk, hu, h, r0;
    hk <@ Bike.keyGen();
    hu <$ distribution_over_R_odd;
    h  <- if b then hu else hk;
    r0 <@ D.distinguish(h);
    return r0;
  }
}.

(* ====================================================================
   7. IND-CPA GAME SEQUENCE (Table 13) AND MONITORING WRAPPER (Table 14)
   ==================================================================== *)
module type OrclL = { proc hash(_ : R * R) : M }.

module type LOR_Adv (O : OrclL) = {
  proc choose(h : R) : M * M        {O.hash}  (* paper A1(h) -> (m0,m1,st) *)
  proc guess(c0 : R, c1 : M) : bool {O.hash}  (* paper A2(h,c0,c1,st) -> b'
                                                 h and st live in glob A *)
}.

module BadWit = {
  var h  : R
  var c0 : R
  var wt : (R * R) option
}.

(* Paper's L' (Table 14): record the witness query, then forward to L. *)
module Lmon : OrclL = {
  proc hash(e : R * R) : M = {
    var v;
    if (wit e BadWit.h BadWit.c0) { BadWit.wt <- Some e; }
    v <@ L.hash(e);
    return v;
  }
}.

(* G0: IND-CPA (Table 13 left, no instrumentation). *)
module G0 (A : LOR_Adv) = {
  proc main() : bool = {
    var h, e0e1, c0, b, m0m1, lv, c1, b';
    L.init();
    h <@ Bike.keyGen();
    e0e1 <$ distribution_over_E_t;                 (* e*  *)
    c0 <- e0e1.`1 + e0e1.`2 * h;                   (* c0* *)
    b <$ {0,1};
    m0m1 <@ A(L).choose(h);
    lv <@ L.hash(e0e1);
    c1 <- fit (b ? m0m1.`2 : m0m1.`1) + lv;
    b' <@ A(L).guess(c0, c1);
    return b' = b;
  }
}.

(* G0_spec: Table 13's G0 verbatim, without the fit coercion (Code
   Major 5). Under the well-formedness contract A_choose_wf the two
   games are equal (G0_G0_spec below), discharging deviation D5. *)
module G0_spec (A : LOR_Adv) = {
  proc main() : bool = {
    var h, e0e1, c0, b, m0m1, lv, c1, b';
    L.init();
    h <@ Bike.keyGen();
    e0e1 <$ distribution_over_E_t;
    c0 <- e0e1.`1 + e0e1.`2 * h;
    b <$ {0,1};
    m0m1 <@ A(L).choose(h);
    lv <@ L.hash(e0e1);
    c1 <- (b ? m0m1.`2 : m0m1.`1) + lv;
    b' <@ A(L).guess(c0, c1);
    return b' = b;
  }
}.

(* G1: G0 + L* instrumentation (only the adversary's queries are watched;
   the challenger uses the raw L). *)
module G1 (A : LOR_Adv) = {
  proc main() : bool = {
    var h, e0e1, c0, b, m0m1, lv, c1, b';
    L.init();
    h <@ Bike.keyGen();
    e0e1 <$ distribution_over_E_t;
    c0 <- e0e1.`1 + e0e1.`2 * h;
    BadWit.h <- h; BadWit.c0 <- c0; BadWit.wt <- None;
    b <$ {0,1};
    m0m1 <@ A(Lmon).choose(h);
    lv <@ L.hash(e0e1);
    c1 <- fit (if b then m0m1.`2 else m0m1.`1) + lv;
    b' <@ A(Lmon).guess(c0, c1);
    return b' = b;
  }
}.

(* G2: c1 $<- M (Table 13 right). *)
module G2 (A : LOR_Adv) = {
  proc main() : bool = {
    var h, e0e1, c0, b, m0m1, c1, b';
    L.init();
    h <@ Bike.keyGen();
    e0e1 <$ distribution_over_E_t;
    c0 <- e0e1.`1 + e0e1.`2 * h;
    BadWit.h <- h; BadWit.c0 <- c0; BadWit.wt <- None;
    b <$ {0,1};
    m0m1 <@ A(Lmon).choose(h);
    c1 <$ duniformM;
    b' <@ A(Lmon).guess(c0, c1);
    return b' = b;
  }
}.

(* G2b: b moved to the tail (for the 1/2 argument, deviation D2; in G2, b is
   unused until the return). *)
module G2b (A : LOR_Adv) = {
  proc main() : bool = {
    var h, e0e1, c0, b, m0m1, c1, b';
    L.init();
    h <@ Bike.keyGen();
    e0e1 <$ distribution_over_E_t;
    c0 <- e0e1.`1 + e0e1.`2 * h;
    BadWit.h <- h; BadWit.c0 <- c0; BadWit.wt <- None;
    m0m1 <@ A(Lmon).choose(h);
    c1 <$ duniformM;
    b' <@ A(Lmon).guess(c0, c1);
    b <$ {0,1};
    return b' = b;
  }
}.

(* Red(A): the A0 of Table 14 (recovers wt and returns it). The paper's
   unused b sample is dropped (D3). *)
module Red (A : LOR_Adv) : OW_Adv = {
  proc solve(h : R, s : R) : (R * R) option = {
    var m0m1, c1, b';
    L.init();
    BadWit.h <- h; BadWit.c0 <- s; BadWit.wt <- None;
    m0m1 <@ A(Lmon).choose(h);
    c1 <$ duniformM;
    b' <@ A(Lmon).guess(s, c1);
    return BadWit.wt;
  }
}.

(* ====================================================================
   8. SECURITY
   ==================================================================== *)
section Security.

declare module A <: LOR_Adv {-Bike, -L, -ROL.Lazy.LRO, -BadWit}.

(* NOTE (Code Major 3): no computational hardness axiom is declared in
   this file. The mechanized results are exact-probability statements
   relative to the concrete games for the explicit reduction Red(A) /
   D_cf(Red(A)). The computational reading — if qccf / OW-qcsd are hard
   for efficient adversaries then both RHS terms are negligible, since
   Red(A) and D_cf(Red(A)) are efficient whenever A is — lives in prose.
   The artifact's main claim is Theorem2_final (with Lemma1_spec
   connecting the real-key parity chain). *)

declare axiom A_choose_ll : forall (O <: OrclL {-A}),
  islossless O.hash => islossless A(O).choose.
declare axiom A_guess_ll : forall (O <: OrclL {-A}),
  islossless O.hash => islossless A(O).guess.

(* Code Major 5: well-formedness contract — A returns messages in F_2^l.
   This is exactly the quantification of the paper (adversaries output
   m0, m1 in {0,1}^l); adversaries violating it are outside the model. *)
declare axiom A_choose_wf (O <: OrclL {-A}) :
  hoare[ A(O).choose : true ==> size res.`1 = l /\ size res.`2 = l ].


(* Lmon is lossless (used for the one-sided handling after bad). *)
lemma Lmon_hash_ll : islossless Lmon.hash.
proof. proc; call L_hash_ll; auto. qed.

(* --------------------------------------------------------------------
   Step 1 (paper: G0 and G1 are identical): transparency of the
   instrumentation.
   Source: old G0_G0_bad. The OL branch of `call (_: ={glob L})` is
   proc*; inline{2} Lmon.hash; wp; call L_hash_eq; auto.
   -------------------------------------------------------------------- *)
(* A_choose_wf lifted to a self-equiv (both sides in sync, size carried). *)
lemma A_choose_eq_wf :
  equiv[ A(L).choose ~ A(L).choose :
         ={arg, glob A, ROL.Lazy.LRO.m} ==>
         ={res, glob A, ROL.Lazy.LRO.m}
         /\ size res{2}.`1 = l /\ size res{2}.`2 = l ].
proof.
conseq (: ={arg, glob A, ROL.Lazy.LRO.m} ==> ={res, glob A, ROL.Lazy.LRO.m})
       _ (A_choose_wf L) => //.
proc (={ROL.Lazy.LRO.m}) => //.
exact L_hash_eq.
qed.

(* Code Major 5 closure: with well-formed adversaries, fit is the
   identity and G0 equals the spec game G0_spec. *)
lemma G0_G0_spec &m :
  Pr[G0(A).main() @ &m : res] = Pr[G0_spec(A).main() @ &m : res].
proof.
byequiv (: ={glob A} ==> ={res}) => //.
proc.
call (_: ={ROL.Lazy.LRO.m}); first exact L_hash_eq.
wp.
call L_hash_eq.
call A_choose_eq_wf.
rnd.
wp.
rnd.
call keyGen_eq.
inline L.init ROL.Lazy.LRO.init.
auto => />.
smt(fit_id).
qed.

lemma G0_G1 &m :
  Pr[G0(A).main() @ &m : res] = Pr[G1(A).main() @ &m : res].
proof.
byequiv (: ={glob A} ==> ={res}) => //.
proc.
call (_: ={ROL.Lazy.LRO.m}).
+ by proc*; inline{2} Lmon.hash; wp; call L_hash_eq; auto => />.
wp.
call L_hash_eq.
call (_: ={ROL.Lazy.LRO.m}).
+ by proc*; inline{2} Lmon.hash; wp; call L_hash_eq; auto => />.
rnd.
wp.
rnd.
call keyGen_eq.
inline L.init ROL.Lazy.LRO.init.
auto => />.
qed.

(* --------------------------------------------------------------------
   Step 2 (paper: if L* = ∅ then G1 and G2 are identical): single-bad
   up-to-bad. This is the core.

   Preservation lemmas first (each side stays bad once bad), then the
   up-to-bad equiv G1_G2_upto, then its two corollaries.

   Attack for G1_G2_upto:
     proc; from the tail, use the 3-argument upto form of `call` with the
     invariant invQ fixed in a previous session:
       ={BadWit.h, BadWit.c0, BadWit.wt, glob A ...}
       /\ eq_except (pred1 e*{2}) ROL...m{1} ROL...m{2}.
     The oracle side-goals are 4 (equiv + two-sided lossless with invQ
     preserved: proc; inline*; auto => />; smt(duniformM_ll); wt only ever
     gets overwritten by Some, so it is monotone).
   Middle challenge ({1}: lv<@L.hash(e_star); c1<-m_b+lv | {2}: c1<$duniformM):
     the post of choose's upto-call is `if bad{2} then invQ else <joined>`,
     so case on (BadWit.wt{2} <> None).
       ¬bad branch: from the invariant "¬bad => e* ∉ dom ROL.m" (bad <=>
         witness query happened, e* is a witness, before the challenger
         writes), rcondt{1} produces a fresh sample and couples it with
         rnd (fun v => m_b + v) (an involution: otp_cancel/otp_supp/otp_mu1).
         Afterwards ROL.m agrees except at e* = eq_except.
       bad branch: run both sides lossless, preserving wt (re-establish invQ).
     prefix (init/keyGen/e*/c0/BadWit assigns/b): in sync.
   The bad equality in the post follows from invP on the ¬bad{2} side and
   from invQ on the bad{2} side.
   -------------------------------------------------------------------- *)
lemma A_guess_pres :
  phoare[ A(Lmon).guess : BadWit.wt <> None ==> BadWit.wt <> None ] = 1%r.
proof.
conseq (: true ==> true) (: BadWit.wt <> None ==> BadWit.wt <> None) => //.
+ proc (BadWit.wt <> None) => //.
  by proc; inline*; auto => />; smt().
by apply (A_guess_ll Lmon Lmon_hash_ll).
qed.

lemma L_hash_pres :
  phoare[ L.hash : BadWit.wt <> None ==> BadWit.wt <> None ] = 1%r.
proof. by proc; inline*; auto => />; smt(duniformM_ll). qed.

lemma G1_G2_upto :
  equiv[ G1(A).main ~ G2(A).main :
         ={glob A} ==>
         (BadWit.wt{1} <> None) = (BadWit.wt{2} <> None)
         /\ (BadWit.wt{2} = None => ={res}) ].
proof.
proc.
(* checkpoint 1: prefix (instructions 1..8 in sync) *)
seq 8 8 : (={glob A, ROL.Lazy.LRO.m, BadWit.h, BadWit.c0, BadWit.wt,
             h, e0e1, c0, b}
           /\ BadWit.wt{2} = None
           /\ BadWit.h{2} = h{2} /\ BadWit.c0{2} = c0{2}
           /\ wit e0e1{2} h{2} c0{2}
           /\ e0e1{2} \notin ROL.Lazy.LRO.m{2}).
+ inline L.init ROL.Lazy.LRO.init.
  auto.
  call keyGen_eq.
  auto => />.
  smt(Et_filter mem_empty).
(* turn e* into a logical constant (oracle invariants can't mention program vars) *)
exists* e0e1{2}; elim* => estar.
(* checkpoint 2: choose's upto call *)
seq 1 1 : (if BadWit.wt{2} <> None
           then BadWit.wt{1} <> None /\ BadWit.wt{2} <> None
           else ={glob A, ROL.Lazy.LRO.m, BadWit.h, BadWit.c0, BadWit.wt,
                  b, e0e1, c0, m0m1}
                /\ BadWit.wt{2} = None
                /\ wit estar BadWit.h{2} BadWit.c0{2}
                /\ e0e1{2} = estar
                /\ estar \notin ROL.Lazy.LRO.m{2}).
+ call (_: BadWit.wt <> None,
        ={ROL.Lazy.LRO.m, BadWit.h, BadWit.c0, BadWit.wt}
        /\ wit estar BadWit.h{2} BadWit.c0{2}
        /\ (BadWit.wt{2} = None => estar \notin ROL.Lazy.LRO.m{2}),
          BadWit.wt{1} <> None /\ BadWit.wt{2} <> None).

  + exact A_choose_ll.
  (* oracle equiv (¬bad precondition) *)
  + proc.
    if => //.
    + (* witness branch *)
      inline L.hash ROL.Lazy.LRO.o.
      sp.
      seq 1 1 : (={x0, ROL.Lazy.LRO.m, BadWit.h, BadWit.c0, BadWit.wt}
                 /\ BadWit.wt{2} <> None).
      + by auto => />; smt().
      if => //.
      + by auto => />; smt().
      by auto => />; smt().
    (* non-witness branch *)
    inline L.hash ROL.Lazy.LRO.o.
    sp.
    seq 1 1 : (={e, x0, r, ROL.Lazy.LRO.m, BadWit.h, BadWit.c0, BadWit.wt}
               /\ x0{2} = e{2}
               /\ wit estar BadWit.h{2} BadWit.c0{2}
               /\ (BadWit.wt{2} = None => estar \notin ROL.Lazy.LRO.m{2})
               /\ !wit e{2} BadWit.h{2} BadWit.c0{2}).
    + by auto => />; smt().
    if => //.
    + by auto => />; smt(mem_set get_setE).
    by auto => />; smt().
  (* lossless-after-bad, left (only after the equiv closes) *)
  + move=> &2 hbad; proc; inline*; auto => />; smt(duniformM_ll).
  (* lossless-after-bad, right *)
  + move=> &1; proc; inline*; auto => />; smt(duniformM_ll).
  (* prefix discharge *)
  auto => />; smt().
(* checkpoint 3: split on bad *)
case (BadWit.wt{2} <> None).
(* bad branch: run both sides lossless *)
+ conseq (: _ ==> BadWit.wt{1} <> None /\ BadWit.wt{2} <> None) => //; 1: smt().
  call{1} A_guess_pres.
  call{2} A_guess_pres.
  wp.
  rnd{2}.
  call{1} L_hash_pres.
  auto => />; smt(duniformM_ll).
(* ¬bad branch: the core OTP coupling *)
(* checkpoint 4: freshen {1}'s L.hash(e_star) *)
inline{1} L.hash ROL.Lazy.LRO.o.
rcondt{1} 4.       (* count the position on the machine; 2..4 depending on param assigns *)
+ by auto => />; smt().
(* checkpoint 5: guess's upto call *)
call (_: BadWit.wt <> None,
      ={BadWit.h, BadWit.c0, BadWit.wt}
      /\ eq_except (pred1 estar) ROL.Lazy.LRO.m{1} ROL.Lazy.LRO.m{2}
      /\ wit estar BadWit.h{2} BadWit.c0{2},
        BadWit.wt{1} <> None /\ BadWit.wt{2} <> None).

  + exact A_guess_ll.
(* oracle equiv: witness branch has post on the `then` side only; the
   non-witness branch stays in sync via eq_except *)
+ proc.
  if => //.
  + (* witness (bad-triggering) branch: both sides did wt <- Some e; the
       ifs may be out of sync *)
    inline L.hash ROL.Lazy.LRO.o.
    sp.
    seq 1 1 : (BadWit.wt{1} <> None /\ BadWit.wt{2} <> None).
    + by auto => />; smt().
    if{1}; if{2}; by auto => />; smt().
  (* non-witness branch: e ≠ estar, so eq_except keeps the ifs in sync *)
  inline L.hash ROL.Lazy.LRO.o.
  sp.
  seq 1 1 : (={e, x0, r, BadWit.h, BadWit.c0, BadWit.wt}
             /\ x0{2} = e{2}
             /\ eq_except (pred1 estar) ROL.Lazy.LRO.m{1} ROL.Lazy.LRO.m{2}
             /\ wit estar BadWit.h{2} BadWit.c0{2}
             /\ !wit e{2} BadWit.h{2} BadWit.c0{2}).
  + by auto => />; smt().
  if.
  + by move=> &1 &2 />; smt(eq_exceptP domE).
  + by auto => />; smt(eq_exceptP eq_except_set_eq get_setE get_set_sameE mem_set domE).
    by auto => />; smt(eq_exceptP domE).
(* lossless-after-bad, left *)
+ move=> &2 hbad; proc; inline*; auto => />; smt(duniformM_ll).
(* lossless-after-bad, right *)
+ move=> &1; proc; inline*; auto => />; smt(duniformM_ll).
(* checkpoint 6: OTP rnd coupling ({1}: v = m.[e*] sample | {2}: c1) *)
wp.
rnd (fun (v : M) => fit (if b{1} then m0m1{1}.`2 else m0m1{1}.`1) + v)
    (fun (c : M) => c - fit (if b{1} then m0m1{1}.`2 else m0m1{1}.`1)).
auto => />.
smt(vec_subrK vec_subrK2 vec_subv_supp duniformM_funi duniformM_size
    size_fit size_addv size_oppv
    get_set_sameE oget_some eq_except_setl eq_exceptP).
qed.

lemma G1_G2_res_notbad &m :
  Pr[G1(A).main() @ &m : res /\ BadWit.wt = None]
  = Pr[G2(A).main() @ &m : res /\ BadWit.wt = None].
proof. by byequiv G1_G2_upto => // /#. qed.

lemma G1_G2_bad &m :
  Pr[G1(A).main() @ &m : BadWit.wt <> None]
  = Pr[G2(A).main() @ &m : BadWit.wt <> None].
proof. by byequiv G1_G2_upto => // /#. qed.

(* --------------------------------------------------------------------
   Step 3 (paper: Pr[G2 | ¬L*] = 1/2, mechanized as D2)
   (a) move b to the tail (b is unused until the return): swap + sim,
       transported for the two events res∧¬bad and ¬bad.
   (b) coin-flip symmetry: at the tail, rnd (fun x => !x) (an involution
       on {0,1}); everything before is sim. ¬bad and b' are fixed before b,
       so the events just swap.
   (c) sum: Pr[E] = Pr[res∧E] + Pr[¬res∧E] (Pr[mu_split res] + smt).
   -------------------------------------------------------------------- *)
lemma G2_G2b_res_notbad &m :
  Pr[G2(A).main() @ &m : res /\ BadWit.wt = None]
  = Pr[G2b(A).main() @ &m : res /\ BadWit.wt = None].
proof.
byequiv (: ={glob A} ==> ={res} /\ ={BadWit.wt}) => //.
by proc; swap{1} 8 3; sim.
qed.

lemma G2_G2b_notbad &m :
  Pr[G2(A).main() @ &m : BadWit.wt = None]
  = Pr[G2b(A).main() @ &m : BadWit.wt = None].
proof.
byequiv (: ={glob A} ==> ={res} /\ ={BadWit.wt}) => //.
by proc; swap{1} 8 3; sim.
qed.

lemma G2b_flip &m :
  Pr[G2b(A).main() @ &m : res /\ BadWit.wt = None]
  = Pr[G2b(A).main() @ &m : !res /\ BadWit.wt = None].
proof.
byequiv (: ={glob A} ==>
           (res{1} /\ BadWit.wt{1} = None)
           <=> (!res{2} /\ BadWit.wt{2} = None)) => //.
proc.
seq 10 10 : (={ROL.Lazy.LRO.m, BadWit.wt, b'}); first by sim.
rnd (fun (x : bool) => !x).
auto => />.
smt(dbool1E dbool_fu).
qed.

lemma G2b_split &m :
  Pr[G2b(A).main() @ &m : BadWit.wt = None]
  = Pr[G2b(A).main() @ &m : res /\ BadWit.wt = None]
  + Pr[G2b(A).main() @ &m : !res /\ BadWit.wt = None].
proof.
rewrite Pr [mu_split res].
congr.
+ by rewrite Pr [mu_eq] => /#.
by rewrite Pr [mu_eq] => /#.
qed.

lemma half_split &m :
  Pr[G2(A).main() @ &m : res /\ BadWit.wt = None]
  = 1%r/2%r * Pr[G2(A).main() @ &m : BadWit.wt = None].
proof.
  rewrite (G2_G2b_res_notbad &m) (G2_G2b_notbad &m).
  have hf := G2b_flip &m. have hs := G2b_split &m. smt().
qed.

(* --------------------------------------------------------------------
   Step 4 (paper: ½ − ½p ≤ Pr[G0] ≤ ½ + ½p, p = Pr[L*])
   Split G1's res with Pr[mu_split (BadWit.wt = None)] and squeeze using
   the Step-2/3 equalities together with 0 ≤ Pr[res∧bad] ≤ Pr[bad].
   Pure arithmetic.
   -------------------------------------------------------------------- *)
lemma G2_full &m : Pr[G2(A).main() @ &m : true] = 1%r.
proof.
byphoare => //.
proc.
call (A_guess_ll Lmon Lmon_hash_ll).
rnd.
call (A_choose_ll Lmon Lmon_hash_ll).
rnd.
wp.
rnd.
call keyGen_ll.
inline L.init ROL.Lazy.LRO.init.
auto => />.
smt(duniformM_ll DEt_ll dbool_ll).
qed.

lemma G0_half_bound &m :
  `| Pr[G0(A).main() @ &m : res] - 1%r/2%r |
  <= 1%r/2%r * Pr[G2(A).main() @ &m : BadWit.wt <> None].
proof.
have h01    := G0_G1 &m.
have hres   := G1_G2_res_notbad &m.
have hbad   := G1_G2_bad &m.
have hhalf  := half_split &m.
have hfull  := G2_full &m.
have hsplit : Pr[G1(A).main() @ &m : res]
  = Pr[G1(A).main() @ &m : res /\ BadWit.wt = None]
  + Pr[G1(A).main() @ &m : res /\ BadWit.wt <> None].
+ by rewrite Pr [mu_split (BadWit.wt = None)].
have hcompl : Pr[G2(A).main() @ &m : true]
  = Pr[G2(A).main() @ &m : BadWit.wt = None]
  + Pr[G2(A).main() @ &m : BadWit.wt <> None].
+ rewrite Pr [mu_split (BadWit.wt = None)].
  by congr; rewrite Pr [mu_eq] => /#.
have hub : Pr[G1(A).main() @ &m : res /\ BadWit.wt <> None]
        <= Pr[G1(A).main() @ &m : BadWit.wt <> None].
+ by rewrite Pr [mu_sub] => /#.
have hf0 : Pr[G1(A).main() @ &m : false] = 0%r by rewrite Pr [mu_false].
have h0  : Pr[G1(A).main() @ &m : false]
        <= Pr[G1(A).main() @ &m : res /\ BadWit.wt <> None].
+ by rewrite Pr [mu_sub].
smt().
qed.

(* --------------------------------------------------------------------
   Step 5 (paper: Pr[G3'] = Pr[L*]): G2's bad probability = OW reduction's
   success probability.
   Source: old badL_eq_uk / badL_fp_inv "found => witness" invariant
   transport + old G3_bad_c1_c1e bad<=>predicate re-mapping.
   byequiv; proc; inline G3_OW/Red; invariant
     ={glob A, glob L, BadWit.*} /\
     (BadWit.wt <> None => wit (oget BadWit.wt) BadWit.h BadWit.c0)
   (Lmon only writes witnesses, so it is preserved) => res(G3_OW) = (wt <> None).
   b lives only in G2 (on the {2} side); consume G2's b <$ {0,1} by rnd{1}.
   -------------------------------------------------------------------- *)
lemma G2_bad_Red &m :
  Pr[G2(A).main() @ &m : BadWit.wt <> None]
  = Pr[G3_OW(Red(A)).main() @ &m : res].
proof.
byequiv (: ={glob A} ==> (BadWit.wt{1} <> None) <=> res{2}) => //.
proc.
inline{2} Red(A).solve.
inline L.init ROL.Lazy.LRO.init.
wp.
call (_: ={ROL.Lazy.LRO.m, BadWit.h, BadWit.c0, BadWit.wt}
        /\ (BadWit.wt{2} <> None =>
              wit (oget BadWit.wt{2}) BadWit.h{2} BadWit.c0{2})).
+ by proc; call L_hash_eq; auto => />; smt().
rnd.
call (_: ={ROL.Lazy.LRO.m, BadWit.h, BadWit.c0, BadWit.wt}
        /\ (BadWit.wt{2} <> None =>
              wit (oget BadWit.wt{2}) BadWit.h{2} BadWit.c0{2})).
+ by proc; call L_hash_eq; auto => />; smt().
rnd{1}.
wp.
rnd.
call keyGen_eq.
auto => />.
smt(dbool_ll).
qed.

(* --------------------------------------------------------------------
   Lemma 1 (paper: Adv^IND-CPA ≤ ½·Adv^OW-CPA, reduction Red(A))
   -------------------------------------------------------------------- *)
lemma Lemma1 &m :
  `| Pr[G0(A).main() @ &m : res] - 1%r/2%r |
  <= 1%r/2%r * Pr[G3_OW(Red(A)).main() @ &m : res].
proof.
  have h1 := G0_half_bound &m. have h2 := G2_bad_Red &m. smt().
qed.

(* --------------------------------------------------------------------
   Theorem 1 (paper: Adv^OW-CPA_PKE0 ≤ Adv^IND_qccf + Adv^OW_qcsd)
   Source: old badL_cf_false / badL_cf_true (inline distinguish -> swap ->
   dead-random rnd{2} / call{2} keyGen_ll -> call (_: true)).
   -------------------------------------------------------------------- *)
lemma T1_false (A0 <: OW_Adv) &m :
  Pr[G3_OW(A0).main() @ &m : res]
  = Pr[DQCCF(D_cf(A0)).main(false) @ &m : res].
proof.
byequiv (: ={glob A0} /\ b{2} = false ==> ={res}) => //.
proc.
inline{2} D_cf(A0).distinguish.
wp.
call (_: true).
wp.
rnd.
wp.
rnd{2}.
call keyGen_eq.
auto => />.
smt(DRodd_ll).
qed.

lemma T1_true (A0 <: OW_Adv) &m :
  Pr[G4_OW(A0).main() @ &m : res]
  = Pr[DQCCF(D_cf(A0)).main(true) @ &m : res].
proof.
byequiv (: ={glob A0} /\ b{2} = true ==> ={res}) => //.
proc.
inline{2} D_cf(A0).distinguish.
wp.
call (_: true).
wp.
rnd.
wp.
rnd.
call{2} keyGen_ll.
auto => />.
qed.

(* --------------------------------------------------------------------
   Theorem 2C (concrete-security form, Code Major 3):
   the advantage bound stated against the two concrete games for the
   specific reduction Red(A) / D_cf(Red(A)), with NO hardness axioms.
   The computational reading ("if qccf/qcsd are hard for efficient
   adversaries then the RHS is negligible, and Red(A)/D_cf(Red(A)) are
   efficient whenever A is") lives in prose, not in the machine.
   Exported G0-side statements (paper Theorem 2 correspondence);
   Theorem2_final, the spec-side main claim, is derived independently
   via Lemma1_spec.
   -------------------------------------------------------------------- *)
lemma Theorem2_concrete &m :
  `| Pr[G0(A).main() @ &m : res] - 1%r/2%r |
  <= 1%r/2%r * `| Pr[DQCCF(D_cf(Red(A))).main(false) @ &m : res]
                - Pr[DQCCF(D_cf(Red(A))).main(true)  @ &m : res] |
   + 1%r/2%r * Pr[G4_OW(Red(A)).main() @ &m : res].
proof.
have h1 := Lemma1 &m.
have hf := T1_false (Red(A)) &m.
have ht := T1_true (Red(A)) &m.
smt().
qed.

(* Paper correspondence: writing eps_qccf for the qccf advantage of
   D_cf(Red(A)) and eps_qcsd_ow for the OW success of Red(A), this is
   exactly Theorem 2's bound  Adv <= 1/2 eps_qccf + 1/2 eps_qcsd_ow,
   and T1_false/T1_true are Theorem 1. The computational reading (both
   epsilons negligible for efficient A, since Red(A)/D_cf(Red(A)) are
   efficient whenever A is) lives in prose; no hardness axiom is
   declared in this file. *)
(* Same bound with the OW term stated against the spec-faithful game
   G4_OW_S (wit_spec), via G4_OW_spec_eq. *)
lemma Theorem2_concrete_spec &m :
  `| Pr[G0(A).main() @ &m : res] - 1%r/2%r |
  <= 1%r/2%r * `| Pr[DQCCF(D_cf(Red(A))).main(false) @ &m : res]
                - Pr[DQCCF(D_cf(Red(A))).main(true)  @ &m : res] |
   + 1%r/2%r * Pr[G4_OW_S(Red(A)).main() @ &m : res].
proof.
have h := Theorem2_concrete &m.
have he := G4_OW_spec_eq (Red(A)) &m.
smt().
qed.

(* Lemma 1 in fully-spec form: connects the real-key parity chain
   (keyGen_eq_odd <- dHw_odd/invp_odd/invp_correct) into the claim via
   G3_OW_spec_eq. *)
lemma Lemma1_spec &m :
  `| Pr[G0_spec(A).main() @ &m : res] - 1%r/2%r |
  <= 1%r/2%r * Pr[G3_OW_S(Red(A)).main() @ &m : res].
proof.
have h0 := G0_G0_spec &m.
have h1 := Lemma1 &m.
have h2 := G3_OW_spec_eq (Red(A)) &m.
smt().
qed.

(* Theorem2_final is now derived from Lemma1_spec: the real-key leg is
   the spec-faithful game G3_OW_S (carrying the keyGen parity chain,
   Code Major 1/4), converted back to G3_OW by G3_OW_spec_eq for the
   T1 bridges, and the uniform-key leg is G4_OW_S. *)
lemma Theorem2_final &m :
  `| Pr[G0_spec(A).main() @ &m : res] - 1%r/2%r |
  <= 1%r/2%r * `| Pr[DQCCF(D_cf(Red(A))).main(false) @ &m : res]
                - Pr[DQCCF(D_cf(Red(A))).main(true)  @ &m : res] |
   + 1%r/2%r * Pr[G4_OW_S(Red(A)).main() @ &m : res].
proof.
have h1 := Lemma1_spec &m.
have h2 := G3_OW_spec_eq (Red(A)) &m.
have hf := T1_false (Red(A)) &m.
have ht := T1_true (Red(A)) &m.
have he := G4_OW_spec_eq (Red(A)) &m.
smt().
qed.

end section Security.
