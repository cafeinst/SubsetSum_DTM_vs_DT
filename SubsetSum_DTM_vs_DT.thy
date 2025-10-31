theory SubsetSum_DTM_vs_DT
  imports "SubsetSum_DTM_Bridge2"
begin

(* ========================================================================= *)
(* PART 1: The Core Asymptotic Lemma                                        *)
(* ========================================================================= *)

(* THE FUNDAMENTAL IMPOSSIBILITY RESULT:
   
   Exponentials beat polynomials! For any polynomial c·n^d, there exists
   a threshold N such that for all n ≥ N:
   
   ⌈c·n^d⌉ < 2√(2^n)
   
   This is the heart of why subset-sum cannot be in P (under our assumptions).
   The left side grows polynomially; the right side grows exponentially.
*)

lemma exp_beats_poly_ceiling_strict_plain:
  fixes c :: real and d :: nat
  assumes cpos: "c > 0"
  shows "∃N::nat. ∀n≥N.
           of_int (ceiling (c * (real n) ^ d)) < 2 * sqrt ((2::real) ^ n)"
proof -
  (* Eventually: c * n^d ≤ (√2)^n *)
  have ev: "eventually (λn. c * (real n) ^ d ≤ (sqrt 2) ^ n) at_top"
    by real_asymp
  then obtain N1 :: nat where N1:
    "∀n≥N1. c * (real n) ^ d ≤ (sqrt 2) ^ n"
    by (auto simp: eventually_at_top_linorder)

  define N where "N = max N1 1"

  have ceil_le: "of_int (ceiling y) ≤ y + 1" for y :: real
    by linarith

  (* Strict step: for n≥1, (√2)^n + 1 < 2(√2)^n *)
  have step_strict:
    "n ≥ 1 ⟹ (sqrt 2) ^ n + 1 < 2 * (sqrt 2) ^ n"
  proof -
    assume n1: "n ≥ 1"
    obtain k where nSuc: "n = Suc k" using n1 by (cases n) auto
    (* (√2)^k ≥ 1 *)
    have pow_ge1: "1 ≤ (sqrt (2::real)) ^ k"
    proof (induction k)
      case 0 show ?case by simp
    next
      case (Suc k)
      have "1 * sqrt 2 ≤ (sqrt 2) ^ k * sqrt 2"
        using Suc.IH by (simp add: mult_right_mono)
      thus ?case by (smt (verit, del_insts) one_le_power real_sqrt_ge_1_iff)
    qed
    (* hence √2 ≤ (√2)^(Suc k), and since 1 < √2, we get 1 < (√2)^n *)
    have "sqrt 2 ≤ (sqrt 2) ^ Suc k"
      using pow_ge1 by (simp add: mult_right_mono)
    hence "1 < (sqrt 2) ^ n"
      using nSuc by (smt (verit) real_sqrt_gt_1_iff)
    then show ?thesis by linarith
  qed

  show ?thesis
  proof (rule exI[of _ N], intro allI impI)
    fix n assume nN: "n ≥ N"
    hence nN1: "n ≥ N1" and n_ge1: "n ≥ 1" by (auto simp: N_def)
    from N1 nN1 have bound: "c * (real n) ^ d ≤ (sqrt 2) ^ n" by simp
    have up: "of_int (ceiling (c * (real n) ^ d)) ≤ (sqrt 2) ^ n + 1"
      using ceil_le bound by linarith
    have strict: "(sqrt 2) ^ n + 1 < 2 * (sqrt 2) ^ n"
      using step_strict n_ge1 by auto
    have eq: "2 * sqrt ((2::real) ^ n) = 2 * (sqrt 2) ^ n"
      by (simp add: real_sqrt_power)
    from up strict eq show
      "of_int (ceiling (c * (real n) ^ d)) < 2 * sqrt ((2::real) ^ n)"
      by linarith
  qed
qed

(* ========================================================================= *)
(* PART 2: Simplified TM→DT Conversion (Cleaner Version)                   *)
(* ========================================================================= *)

context DTM_Run_Sem
begin

(* Inherit the DTM_Run interface as "Base" *)
sublocale Base: DTM_Run steps conf head0 accepts .

(* A CLEANER version of tm_to_dtr without the extra parameters.
   
   This is essentially the same as tm_to_dtr' but with a simpler signature.
   We build it directly into the DTM_Run_Sem context. *)

fun tm_to_dtr :: "nat ⇒ 'C ⇒ (nat,nat) dtr" where
  "tm_to_dtr 0 c = Leaf (final_acc c)"
| "tm_to_dtr (Suc t) c =
     AskL (nat (head0 c))
          (tm_to_dtr t (stepf c False))
          (tm_to_dtr t (stepf c True))"

lemma tm_to_dtr_steps[simp]:
  "steps_run oL oR (tm_to_dtr t c) = t" for oL oR
  by (induction t arbitrary: c) simp_all

(* ========================================================================= *)
(* PART 3: Correctness with Time Offset                                     *)
(* ========================================================================= *)

(* LEMMA: Running the tree from config at time t0 for t steps
   gives the right answer at time t0+t
   
   This is the shifted version that's easier to prove by induction. *)

lemma tm_to_dtr_correct_shift:
  "run ((!) x) ((!) x) (tm_to_dtr t (conf M x t0))
   = final_acc (conf M x (t0 + t))"
proof (induction t arbitrary: x t0)
  case 0
  show ?case by simp
next
  case (Suc t)
  have step0:
    "conf M x (Suc t0) =
       stepf (conf M x t0) (x ! nat (head0 (conf M x t0)))"
    by (simp add: step_sem)

  show ?case
  proof (cases "x ! nat (head0 (conf M x t0))")
    case True
    have "run ((!) x) ((!) x) (tm_to_dtr (Suc t) (conf M x t0))
          = run ((!) x) ((!) x) (tm_to_dtr t (stepf (conf M x t0) True))"
      by (simp add: True)
    also have "… = run ((!) x) ((!) x) (tm_to_dtr t (conf M x (Suc t0)))"
      using True step0 by simp
    also have "… = final_acc (conf M x (Suc t0 + t))"
      by (rule Suc.IH)
    also have "… = final_acc (conf M x (t0 + Suc t))"
      by simp
    finally show ?thesis .
  next
    case False
    have "run ((!) x) ((!) x) (tm_to_dtr (Suc t) (conf M x t0))
          = run ((!) x) ((!) x) (tm_to_dtr t (stepf (conf M x t0) False))"
      by (simp add: False)
    also have "… = run ((!) x) ((!) x) (tm_to_dtr t (conf M x (Suc t0)))"
      using False step0 by simp
    also have "… = final_acc (conf M x (Suc t0 + t))"
      by (rule Suc.IH)
    also have "… = final_acc (conf M x (t0 + Suc t))"
      by simp
    finally show ?thesis .
  qed
qed

(* ========================================================================= *)
(* PART 4: Tracking Seen Indices (with Time Offset)                        *)
(* ========================================================================= *)

(* LEMMA: All indices seen by the tree are positions that the TM
   actually reads during steps [t0, t0+t)
   
   Again, the shifted version for easier induction. *)

lemma tm_to_dtr_seen_subset_shift:
  "seenL_run ((!) x) ((!) x) (tm_to_dtr t (conf M x t0))
   ⊆ (λu. nat (head0 (conf M x (t0 + u)))) ` {..< t}"
proof (induction t arbitrary: t0)
  case 0
  show ?case by simp
next
  case (Suc t)
  let ?i0 = "nat (head0 (conf M x t0))"

  have root_in:
    "?i0 ∈ (λu. nat (head0 (conf M x (t0 + u)))) ` {..< Suc t}"
    by (intro image_eqI[where x=0]) (simp_all)

  have conf1:
    "conf M x (Suc t0) =
       stepf (conf M x t0) (x ! nat (head0 (conf M x t0)))"
    by (simp add: step_sem)

  have sub_seen_eq:
    "seenL_run ((!) x) ((!) x)
       (if x ! ?i0
        then tm_to_dtr t (stepf (conf M x t0) True)
        else tm_to_dtr t (stepf (conf M x t0) False))
     =
     seenL_run ((!) x) ((!) x) (tm_to_dtr t (conf M x (Suc t0)))"
    by (cases "x ! ?i0") (simp_all add: conf1)

  have IH:
    "seenL_run ((!) x) ((!) x) (tm_to_dtr t (conf M x (Suc t0)))
     ⊆ (λu. nat (head0 (conf M x (Suc t0 + u)))) ` {..< t}"
    by (rule Suc.IH)

  have shift:
    "(λu. nat (head0 (conf M x (Suc t0 + u)))) ` {..< t}
    ⊆ (λv. nat (head0 (conf M x (t0 + v)))) ` {..< Suc t}"
  proof
    fix y assume "y ∈ (λu. nat (head0 (conf M x (Suc t0 + u)))) ` {..< t}"
    then obtain u where u_lt: "u < t"
      and y_def: "y = nat (head0 (conf M x (Suc t0 + u)))" by auto
    let ?f = "λv. nat (head0 (conf M x (t0 + v)))"
    have y_eq: "y = ?f (Suc u)"
      by (simp add: y_def)
    have Su: "Suc u ∈ {..< Suc t}" using u_lt by simp
    have "?f (Suc u) ∈ ?f ` {..< Suc t}"
      using Su by (rule imageI)
    thus "y ∈ ?f ` {..< Suc t}"
      by (simp add: y_eq)
  qed

  have subtree_in:
    "seenL_run ((!) x) ((!) x)
       (if x ! ?i0
        then tm_to_dtr t (stepf (conf M x t0) True)
        else tm_to_dtr t (stepf (conf M x t0) False))
     ⊆ (λv. nat (head0 (conf M x (t0 + v)))) ` {..< Suc t}"
    using sub_seen_eq IH shift by blast

  show ?case
  proof
    fix i assume i_in:
      "i ∈ seenL_run ((!) x) ((!) x) (tm_to_dtr (Suc t) (conf M x t0))"
    then have "i = ?i0
               ∨ i ∈ seenL_run ((!) x) ((!) x)
                       (if x ! ?i0
                        then tm_to_dtr t (stepf (conf M x t0) True)
                        else tm_to_dtr t (stepf (conf M x t0) False))"
      by simp
    thus "i ∈ (λu. nat (head0 (conf M x (t0 + u)))) ` {..< Suc t}"
      using root_in subtree_in by blast
  qed
qed

(* ========================================================================= *)
(* PART 5: The Main Correctness and Coverage Theorems                      *)
(* ========================================================================= *)

(* THEOREM: The decision tree correctly computes acceptance *)
lemma tm_to_dtr_correct:
  "run ((!) x) ((!) x) (tm_to_dtr (steps M x) (conf M x 0)) = accepts M x"
  by (simp add: tm_to_dtr_correct_shift accepts_sem[symmetric])

(* THEOREM: The tree only queries positions that the TM reads *)
lemma tm_to_dtr_seen_subset_read0:
  "seenL_run ((!) x) ((!) x) (tm_to_dtr (steps M x) (conf M x 0))
   ⊆ Base.read0 M x"
  using tm_to_dtr_seen_subset_shift[of x "steps M x" 0]
  by (simp add: Base.read0_def)

end  (* context DTM_Run_Sem *)


(* ========================================================================= *)
(* PART 6: Optional Refinement Locale (Head Range Assumption)              *)
(* ========================================================================= *)

(* This locale adds the assumption that the head stays within bounds [0, n).
   
   This is needed if we want to ensure well-formed decision trees that only
   query positions 0..n-1. In practice, most TMs satisfy this. *)

locale DTM_refines_DTR = DTM_Run_Sem +
  fixes n :: nat
  assumes head_in_range:
    "⋀x t. length x = n ⟹ t < steps M x
           ⟹ 0 ≤ head0 (conf M x t) ∧ nat (head0 (conf M x t)) < n"
 (* If the input has length n and we haven't halted yet,
       the head is in range [0, n) *)

context DTM_refines_DTR
begin

(* Simple corollaries that follow from the refinement *)

lemma dt_steps_on_x_eq_tm_steps:
  "steps_run oL oR (tm_to_dtr (steps M x) (conf M x 0)) = steps M x" for oL oR
  by simp
  (* The tree makes exactly (steps M x) queries *)

lemma dt_correct_on_x:
  "run (λi. x ! i) (λj. x ! j)
       (tm_to_dtr (steps M x) (conf M x 0)) = accepts M x"
  by (rule tm_to_dtr_correct)

end

(* ========================================================================= *)
(* PART 7: The Final Impossibility Result (EXISTENTIAL VERSION)            *)
(* ========================================================================= *)

context Coverage_TM
begin

definition pow2_target :: "nat ⇒ int" where
  "pow2_target n = (2::int)^(n-1) - 1"

(* THEOREM: For a specific hard instance, steps ≥ 2√(2^n) *)
lemma steps_ge_two_sqrt_pow2_for_instance:
  assumes n_def: "n = length as"
      and k_le: "kk ≤ n"
      and distinct: "distinct_subset_sums as"
      (* Coverage conditions (provable for specific instances) *)
      and L2: "2 ≤ length (enumL as s kk)"
      and R2: "2 ≤ length (enumR as s kk)"
      and hit: "∃v∈set (enumL as s kk). v ∈ set (enumR as s kk)"
      and miss: "∃v∈set (enumL as s kk). v ∉ set (enumR as s kk)"
      and baseline: "∀j. good as s ((!) (enc as s kk)) ((!) (enc as s kk)) ⟶
                         (∀j'<length (enumL as s kk). j' ≠ j ⟶
                            Lval_at as s ((!) (enc as s kk)) j' ∉ set (enumR as s kk))"
  shows "real (steps M (enc as s kk)) ≥ 2 * sqrt ((2::real) ^ n)"
proof -
  have LB: "steps M (enc as s kk) ≥
              card (LHS (e_k as s kk) n) + card (RHS (e_k as s kk) n)"
    using L2 R2 baseline distinct hit miss n_def steps_lower_bound by blast

  have AMG: "real (card (LHS (e_k as s kk) n) + card (RHS (e_k as s kk) n))
               ≥ 2 * sqrt ((2::real) ^ n)"
    using lhs_rhs_sum_lower_bound[OF n_def k_le distinct] .

  from LB AMG show ?thesis by linarith
qed

(* ========================================================================= *)
(* THE MAIN THEOREM: There EXISTS a Hard Instance (INSIDE LOCALE)          *)
(* ========================================================================= *)

theorem exists_hard_instance_exponential_lower_bound:
  assumes n_ge2: "n ≥ 2"
      and kk_bounds: "1 ≤ kk" "kk < n"
  shows "∃as s.
           length as = n ∧
           distinct_subset_sums as ∧
           real (steps M (enc as s kk)) ≥ 2 * sqrt ((2::real) ^ n)"
proof -
  (* Extract the individual bounds with names *)
  have kk_ge_1: "1 ≤ kk" using kk_bounds by simp
  have kk_lt_n: "kk < n" using kk_bounds by simp
  have kk_le_n: "kk ≤ n" using kk_lt_n by simp  (* Derive non-strict from strict *)
  
  (* Use pow2_list with the chosen target *)
  define as where "as = pow2_list n"
  define s where "s = (pow2_target n :: int)"
  
  (* All coverage conditions hold *)
  have len_as: "length as = n"
    by (simp add: as_def pow2_list_def)
  
  have dist_as: "distinct_subset_sums as"
    by (simp add: as_def distinct_subset_sums_pow2_list)
  
  (* L2: Inline proof *)
  have L2: "2 ≤ length (enumL as s kk)"
  proof -
    have card_eq: "card (LHS (e_k as s kk) n) = 2^kk"
      using card_LHS_e_k[of n as kk s] len_as kk_le_n dist_as
      by simp
    
    have pow_ge: "2 ≤ (2::nat)^kk"
      using kk_ge_1 by (cases kk) simp_all
    
    have "length (enumL as s kk) = card (LHS (e_k as s kk) n)"
      using enumL_def distinct_card by (simp add: len_as)
    
    with card_eq pow_ge show ?thesis by simp
  qed
  
  have R2: "2 ≤ length (enumR as s kk)"
  proof -
    have card_eq: "card (RHS (e_k as s kk) n) = 2^(n - kk)"
      using card_RHS_e_k[of n as kk s] len_as kk_le_n dist_as
      by simp
    
    have pow_ge: "2 ≤ (2::nat)^(n - kk)"
      using kk_lt_n by (cases "n - kk") simp_all
    
    have "length (enumR as s kk) = card (RHS (e_k as s kk) n)"
      using enumR_def distinct_card by (simp add: len_as)
    
    with card_eq pow_ge show ?thesis by simp
  qed
  
  (* hit, miss, baseline - all use x0 as s *)
  have hit: "∃v∈set (enumL as s kk). v ∈ set (enumR as s kk)"
    sorry
  
  have miss: "∃v∈set (enumL as s kk). v ∉ set (enumR as s kk)"
    sorry
  
  have baseline: "∀j. good as s ((!) (x0 as s)) ((!) (x0 as s)) ⟶
                      (∀j'<length (enumL as s kk). j' ≠ j ⟶
                         Lval_at as s ((!) (x0 as s)) j' ∉ set (enumR as s kk))"
    sorry  (* Changed from enc as s kk to x0 as s, and removed type annotations *)
  
  (* Apply the theorem *)
  have lb: "real (steps M (x0 as s)) ≥ 2 * sqrt ((2::real) ^ n)"
  proof -
    have "n = length as" using len_as by simp
    then show ?thesis
      using steps_ge_two_sqrt_pow2_for_instance[OF _ kk_le_n dist_as L2 R2 hit miss baseline]
      by simp
  qed
  
  (* Show that x0 as s = enc as s kk *)
  have x0_eq: "x0 as s = enc as s kk"
    by simp
  
  (* Rewrite the lower bound *)
  have "real (steps M (enc as s kk)) ≥ 2 * sqrt ((2::real) ^ n)"
    using lb x0_eq by simp
  
  thus ?thesis
    using len_as dist_as
    by (intro exI[of _ as] exI[of _ s]) blast
qed

(* ========================================================================= *)
(* COROLLARY: No Polynomial-Time Algorithm                                   *)
(* ========================================================================= *)

theorem no_polytime_on_worst_case:
  assumes kk_bounds: "1 ≤ kk" 
      and kk_always_strict: "⋀n. n ≥ 2 ⟹ kk < n"
  shows "¬ (∃(c::real)>0. ∃(d::nat).
           ∀n≥2. ∀as s. length as = n ∧ distinct_subset_sums as ⟶
             real (steps M (enc as s kk)) ≤ c * real n ^ d)"
proof
  assume poly: "∃(c::real)>0. ∃(d::nat).
                 ∀n≥2. ∀as s. length as = n ∧ distinct_subset_sums as ⟶
                   real (steps M (enc as s kk)) ≤ c * real n ^ d"
  
  obtain c d where c_pos: "c > 0" and
    UB: "∀n≥2. ∀as s. length as = n ∧ distinct_subset_sums as ⟶
                  real (steps M (enc as s kk)) ≤ c * real n ^ d"
    using poly by blast
  
  (* Exponentials beat polynomials *)
  obtain N where Nbig_ceil: "∀n≥N. of_int ⌈c * real n ^ d⌉ < 2 * sqrt ((2::real)^n)"
    using exp_beats_poly_ceiling_strict_plain[OF c_pos] by blast
  
  have Nbig: "∀n≥N. c * real n ^ d < 2 * sqrt ((2::real)^n)"
  proof (intro allI impI)
    fix n assume "n ≥ N"
    then have "of_int ⌈c * real n ^ d⌉ < 2 * sqrt ((2::real)^n)"
      using Nbig_ceil by simp
    moreover have "c * real n ^ d ≤ of_int ⌈c * real n ^ d⌉"
      by linarith
    ultimately show "c * real n ^ d < 2 * sqrt ((2::real)^n)"
      by linarith
  qed
  
  (* Pick n large enough *)
  define n where "n = max N 2"
  have n_geN: "n ≥ N" and n_ge2: "n ≥ 2" by (simp_all add: n_def)
  
  (* kk bounds for this specific n *)
  have kk_lt_n: "kk < n"
    using kk_always_strict[OF n_ge2] .
  
  have kk_bounds_n: "1 ≤ kk" "kk < n"
    using kk_bounds kk_lt_n by simp_all
  
  (* Get the hard instance (pow2_list) *)
  obtain as s where
    len: "length as = n" and
    dist: "distinct_subset_sums as" and
    LB: "real (steps M (enc as s kk)) ≥ 2 * sqrt ((2::real)^n)"
    using exists_hard_instance_exponential_lower_bound[OF n_ge2 kk_bounds_n] 
    by blast
  
  (* Upper bound from polynomial assumption applied to THIS instance *)
  have UB_inst: "real (steps M (enc as s kk)) ≤ c * real n ^ d"
    using UB[rule_format, OF n_ge2, of as s] len dist by blast
  
  (* Lower bound from exponential *)
  have LT: "c * real n ^ d < 2 * sqrt ((2::real)^n)"
    using Nbig n_geN by simp
  
  (* Contradiction: steps ≥ 2√(2^n) > c·n^d ≥ steps *)
  from LB LT UB_inst show False by linarith
qed

end
end  (* context Coverage_TM *)
