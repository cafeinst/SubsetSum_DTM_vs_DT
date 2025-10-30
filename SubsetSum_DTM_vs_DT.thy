theory SubsetSum_DTM_vs_DT
  imports "SubsetSum_DTM_Bridge" "SubsetSum_DecisionTree"
begin

(* ========================================================================= *)
(* PART 1: The Core Asymptotic Lemma                                        *)
(* ========================================================================= *)

(* THE FUNDAMENTAL IMPOSSIBILITY RESULT:
   
   Exponentials beat polynomials! For any polynomial c\<sqdot>n^d, there exists
   a threshold N such that for all n \<ge> N:
   
   \<lceil>c\<sqdot>n^d\<rceil> < 2\<surd>(2^n)
   
   This is the heart of why subset-sum cannot be in P (under our assumptions).
   The left side grows polynomially; the right side grows exponentially.
*)

lemma exp_beats_poly_ceiling_strict_plain:
  fixes c :: real and d :: nat
  assumes cpos: "c > 0"
  shows "\<exists>N::nat. \<forall>n\<ge>N.
           of_int (ceiling (c * (real n) ^ d)) < 2 * sqrt ((2::real) ^ n)"
proof -
  (* Eventually: c * n^d \<le> (\<surd>2)^n *)
  have ev: "eventually (\<lambda>n. c * (real n) ^ d \<le> (sqrt 2) ^ n) at_top"
    by real_asymp
  then obtain N1 :: nat where N1:
    "\<forall>n\<ge>N1. c * (real n) ^ d \<le> (sqrt 2) ^ n"
    by (auto simp: eventually_at_top_linorder)

  define N where "N = max N1 1"

  have ceil_le: "of_int (ceiling y) \<le> y + 1" for y :: real
    by linarith

  (* Strict step: for n\<ge>1, (\<surd>2)^n + 1 < 2(\<surd>2)^n *)
  have step_strict:
    "n \<ge> 1 \<Longrightarrow> (sqrt 2) ^ n + 1 < 2 * (sqrt 2) ^ n"
  proof -
    assume n1: "n \<ge> 1"
    obtain k where nSuc: "n = Suc k" using n1 by (cases n) auto
    (* (\<surd>2)^k \<ge> 1 *)
    have pow_ge1: "1 \<le> (sqrt (2::real)) ^ k"
    proof (induction k)
      case 0 show ?case by simp
    next
      case (Suc k)
      have "1 * sqrt 2 \<le> (sqrt 2) ^ k * sqrt 2"
        using Suc.IH by (simp add: mult_right_mono)
      thus ?case by (smt (verit, del_insts) one_le_power real_sqrt_ge_1_iff)
    qed
    (* hence \<surd>2 \<le> (\<surd>2)^(Suc k), and since 1 < \<surd>2, we get 1 < (\<surd>2)^n *)
    have "sqrt 2 \<le> (sqrt 2) ^ Suc k"
      using pow_ge1 by (simp add: mult_right_mono)
    hence "1 < (sqrt 2) ^ n"
      using nSuc by (smt (verit) real_sqrt_gt_1_iff)
    then show ?thesis by linarith
  qed

  show ?thesis
  proof (rule exI[of _ N], intro allI impI)
    fix n assume nN: "n \<ge> N"
    hence nN1: "n \<ge> N1" and n_ge1: "n \<ge> 1" by (auto simp: N_def)
    from N1 nN1 have bound: "c * (real n) ^ d \<le> (sqrt 2) ^ n" by simp
    have up: "of_int (ceiling (c * (real n) ^ d)) \<le> (sqrt 2) ^ n + 1"
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
(* PART 2: Simplified TM\<rightarrow>DT Conversion (Cleaner Version)                   *)
(* ========================================================================= *)

context DTM_Run_Sem
begin

(* Inherit the DTM_Run interface as "Base" *)
sublocale Base: DTM_Run steps conf head0 accepts .

(* A CLEANER version of tm_to_dtr without the extra parameters.
   
   This is essentially the same as tm_to_dtr' but with a simpler signature.
   We build it directly into the DTM_Run_Sem context. *)

fun tm_to_dtr :: "nat \<Rightarrow> 'C \<Rightarrow> (nat,nat) dtr" where
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
    also have "\<dots> = run ((!) x) ((!) x) (tm_to_dtr t (conf M x (Suc t0)))"
      using True step0 by simp
    also have "\<dots> = final_acc (conf M x (Suc t0 + t))"
      by (rule Suc.IH)
    also have "\<dots> = final_acc (conf M x (t0 + Suc t))"
      by simp
    finally show ?thesis .
  next
    case False
    have "run ((!) x) ((!) x) (tm_to_dtr (Suc t) (conf M x t0))
          = run ((!) x) ((!) x) (tm_to_dtr t (stepf (conf M x t0) False))"
      by (simp add: False)
    also have "\<dots> = run ((!) x) ((!) x) (tm_to_dtr t (conf M x (Suc t0)))"
      using False step0 by simp
    also have "\<dots> = final_acc (conf M x (Suc t0 + t))"
      by (rule Suc.IH)
    also have "\<dots> = final_acc (conf M x (t0 + Suc t))"
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
   \<subseteq> (\<lambda>u. nat (head0 (conf M x (t0 + u)))) ` {..< t}"
proof (induction t arbitrary: t0)
  case 0
  show ?case by simp
next
  case (Suc t)
  let ?i0 = "nat (head0 (conf M x t0))"

  have root_in:
    "?i0 \<in> (\<lambda>u. nat (head0 (conf M x (t0 + u)))) ` {..< Suc t}"
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
     \<subseteq> (\<lambda>u. nat (head0 (conf M x (Suc t0 + u)))) ` {..< t}"
    by (rule Suc.IH)

  have shift:
    "(\<lambda>u. nat (head0 (conf M x (Suc t0 + u)))) ` {..< t}
    \<subseteq> (\<lambda>v. nat (head0 (conf M x (t0 + v)))) ` {..< Suc t}"
  proof
    fix y assume "y \<in> (\<lambda>u. nat (head0 (conf M x (Suc t0 + u)))) ` {..< t}"
    then obtain u where u_lt: "u < t"
      and y_def: "y = nat (head0 (conf M x (Suc t0 + u)))" by auto
    let ?f = "\<lambda>v. nat (head0 (conf M x (t0 + v)))"
    have y_eq: "y = ?f (Suc u)"
      by (simp add: y_def)
    have Su: "Suc u \<in> {..< Suc t}" using u_lt by simp
    have "?f (Suc u) \<in> ?f ` {..< Suc t}"
      using Su by (rule imageI)
    thus "y \<in> ?f ` {..< Suc t}"
      by (simp add: y_eq)
  qed

  have subtree_in:
    "seenL_run ((!) x) ((!) x)
       (if x ! ?i0
        then tm_to_dtr t (stepf (conf M x t0) True)
        else tm_to_dtr t (stepf (conf M x t0) False))
     \<subseteq> (\<lambda>v. nat (head0 (conf M x (t0 + v)))) ` {..< Suc t}"
    using sub_seen_eq IH shift by blast

  show ?case
  proof
    fix i assume i_in:
      "i \<in> seenL_run ((!) x) ((!) x) (tm_to_dtr (Suc t) (conf M x t0))"
    then have "i = ?i0
               \<or> i \<in> seenL_run ((!) x) ((!) x)
                       (if x ! ?i0
                        then tm_to_dtr t (stepf (conf M x t0) True)
                        else tm_to_dtr t (stepf (conf M x t0) False))"
      by simp
    thus "i \<in> (\<lambda>u. nat (head0 (conf M x (t0 + u)))) ` {..< Suc t}"
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
   \<subseteq> Base.read0 M x"
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
    "\<And>x t. length x = n \<Longrightarrow> t < steps M x
           \<Longrightarrow> 0 \<le> head0 (conf M x t) \<and> nat (head0 (conf M x t)) < n"
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
  "run (\<lambda>i. x ! i) (\<lambda>j. x ! j)
       (tm_to_dtr (steps M x) (conf M x 0)) = accepts M x"
  by (rule tm_to_dtr_correct)

end

(* ========================================================================= *)
(* PART 7: The Final Impossibility Result                                   *)
(* ========================================================================= *)

context Coverage_TM
begin

(* THEOREM: steps M (enc as s kk) \<ge> 2\<surd>(2^n)
   
   This combines:
   - steps_lower_bound: steps \<ge> |LHS| + |RHS| (from coverage)
   - lhs_rhs_sum_lower_bound: |LHS| + |RHS| \<ge> 2\<surd>(2^n) (from AM-GM)
*)

lemma steps_ge_two_sqrt_pow2:
  assumes n_def: "n = length as"
      and k_le:  "kk \<le> n"
      and distinct: "distinct_subset_sums as"
  shows "real (steps M (enc as s kk)) \<ge> 2 * sqrt ((2::real) ^ n)"
proof -

(* From Coverage_TM: Every block is touched \<rightarrow> steps \<ge> |LHS| + |RHS| *)
  have LB:
    "steps M (enc as s kk) \<ge>
       card (LHS (e_k as s kk) n) + card (RHS (e_k as s kk) n)"
    by (rule steps_lower_bound[OF n_def distinct])

  (* From AM-GM + Lemma 2: |LHS| + |RHS| \<ge> 2\<surd>(2^n) *)
  have AMG:
    "real (card (LHS (e_k as s kk) n) + card (RHS (e_k as s kk) n))
       \<ge> 2 * sqrt ((2::real) ^ n)"
    using lhs_rhs_sum_lower_bound[OF n_def k_le distinct] .

  (* Chain them together *)
  from LB AMG show ?thesis by linarith
qed

(* ========================================================================= *)
(* THE MAIN THEOREM: No Polynomial-Time Algorithm!                          *)
(* ========================================================================= *)

(* THEOREM: There is NO polynomial-time TM that solves subset-sum
   for the distinct-subset-sums family.
   
   Proof by contradiction:
   - Suppose \<exists>c,d such that steps \<le> c\<sqdot>n^d for all distinct instances
   - By exp_beats_poly, \<exists>N such that for n\<ge>N: c\<sqdot>n^d < 2\<surd>(2^n)
   - But for the powers-of-two instance at n\<ge>N:
     steps \<ge> 2\<surd>(2^n) (by steps_ge_two_sqrt_pow2)
     steps \<le> c\<sqdot>n^d (by assumption)
   - Contradiction!
*)

theorem no_polytime_in_n_on_distinct_family:
  shows "\<not> (\<exists>(c::real)>0. \<exists>(d::nat).
           \<forall>as s. distinct_subset_sums as \<longrightarrow>
             steps M (enc as s kk) \<le> nat \<lceil> c * real (length as) ^ d \<rceil>)"
proof
  assume ex_poly: "\<exists>(c::real)>0. \<exists>(d::nat).
          \<forall>as s. distinct_subset_sums as \<longrightarrow>
            steps M (enc as s kk) \<le> nat \<lceil> c * real (length as) ^ d \<rceil>"
  then obtain c d where
    cpos: "c > 0" and
    UB: "\<forall>as s. distinct_subset_sums as \<longrightarrow>
                  steps M (enc as s kk) \<le> nat \<lceil> c * real (length as) ^ d \<rceil>"
    by blast

  (* By exp_beats_poly: eventually c\<sqdot>n^d < 2\<surd>(2^n) *)
  from exp_beats_poly_ceiling_strict_plain[OF cpos]
  obtain N :: nat where
    Nbig: "\<forall>n\<ge>N. of_int \<lceil> c * real n ^ d \<rceil> < 2 * sqrt ((2::real) ^ n)" by blast

 (* Pick n large enough: n \<ge> max(N, kk) *)
  define n where "n = max N kk"
  have n_geN: "N \<le> n" and kk_le: "kk \<le> n" by (simp_all add: n_def)

 (* Use the powers-of-two instance of size n *)
  let ?as = "pow2_list n"
  have len_as: "length (pow2_list n) = n"
    by (simp add: pow2_list_def)
  have distinct: "distinct_subset_sums ?as"
    by (rule distinct_subset_sums_pow2_list)

  (* LOWER BOUND: From coverage + AM-GM *)
  have LB:
  "2 * sqrt ((2::real) ^ n) \<le> real (steps M (enc (pow2_list n) s kk))"
    using steps_ge_two_sqrt_pow2[of n "pow2_list n" s,
    OF _ kk_le distinct_subset_sums_pow2_list]
    by (simp add: len_as)

  (* UPPER BOUND: From the polynomial assumption *)
  have UBn:
    "steps M (enc ?as s kk) \<le> nat \<lceil> c * real (length ?as) ^ d \<rceil>"
    using UB distinct by blast
  hence UBn_real:
    "real (steps M (enc ?as s kk)) \<le> of_int \<lceil> c * real n ^ d \<rceil>"
    by (smt (verit) LB Nbig ceiling_mono cpos distinct kk_le 
        landau_omega.R_mult_left_mono n_geN of_nat_le_0_iff 
        of_nat_le_iff of_nat_less_0_iff of_nat_less_of_int_iff 
        of_nat_nat power_less_imp_less_base real_sqrt_gt_zero 
        split_nat steps_ge_two_sqrt_pow2 zero_less_power)

  (* But c\<sqdot>n^d < 2\<surd>(2^n) for n \<ge> N *)
  have LT:
    "of_int \<lceil> c * real n ^ d \<rceil> < 2 * sqrt ((2::real) ^ n)"
    using Nbig n_geN by blast

  (* Contradiction: steps \<le> c\<sqdot>n^d < 2\<surd>(2^n) \<le> steps *)
  from LB UBn_real LT show False
    by linarith
qed


(* ========================================================================= *)
(* COROLLARY: Concrete Worst-Case Lower Bound                               *)
(* ========================================================================= *)

(* Optional tidier statement: Any TM satisfying our assumptions
   has worst-case time at least \<lceil>2\<surd>(2^n)\<rceil> on instances of size n. *)

corollary dtm_worst_case_sqrt_bound:
  assumes "n = length as" "kk \<le> n" "distinct_subset_sums as"
  shows   "steps M (enc as s kk) \<ge> nat \<lceil> 2 * sqrt ((2::real)^n) \<rceil>"
    using assms(1) assms(2) assms(3) steps_ge_two_sqrt_pow2 by auto

end
end  (* theory *)
