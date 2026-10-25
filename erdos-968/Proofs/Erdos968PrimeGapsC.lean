module

/-
Copyright 2025-2026 The Formal Conjectures Authors.
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

public import Mathlib
public import Erdos968PrimeGapsA
public import Erdos968PrimeGapsB

@[expose] public section

section File_OpenAIPrimeGaps_AdditiveSieve

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

theorem symmetric_kernel_quadratic_le {ι : Type*} (s : Finset ι) (a : ι→ℝ)
    (w : ι→ι→ℝ) (hw : ∀ i∈s,∀ j∈s,0≤w i j)
    (hs : ∀ i∈s,∀ j∈s,w i j=w j i) :
    (∑ i∈s,∑ j∈s,a i*a j*w i j)≤∑ i∈s,a i^2*(∑ j∈s,w i j) := by
  have hh : (∑ i∈s,∑ j∈s,a i*a j*w i j)≤
      ∑ i∈s,∑ j∈s,(a i^2*w i j+a j^2*w i j)/2 := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have h := mul_nonneg (sq_nonneg (a i-a j)) (hw i hi j hj)
    nlinarith
  have hswap : (∑ i∈s,∑ j∈s,a j^2*w i j)=(∑ i∈s,∑ j∈s,a i^2*w i j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hs j hj i hi]
  calc
    _ ≤ _ := hh
    _ = _ := by
      simp_rw [←Finset.sum_div,Finset.sum_add_distrib]
      rw [hswap]
      simp only [Finset.mul_sum]
      ring

theorem norm_sum_smul_sq_le_gram {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (s : Finset ι) (v : ι→E) (c : ι→ℂ) :
    ‖∑ i∈s,c i • v i‖^2≤∑ i∈s,‖c i‖^2*(∑ j∈s,‖inner ℂ (v i) (v j)‖) := by
  calc
    _ = ∑ i∈s,∑ j∈s,(conj (c i)*(c j*inner ℂ (v i) (v j))).re := by
      rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜:=ℂ)]
      simp only [sum_inner,inner_sum,inner_smul_left,inner_smul_right,Finset.mul_sum,map_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change (c j * (conj (c i) * inner ℂ (v i) (v j))).re = _
      congr 1
      ring
    _ ≤ ∑ i∈s,∑ j∈s,‖c i‖*‖c j‖*‖inner ℂ (v i) (v j)‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [norm_mul,Complex.norm_conj,mul_assoc] using
        Complex.re_le_norm (conj (c i)*(c j*inner ℂ (v i) (v j)))
    _ ≤ _ := symmetric_kernel_quadratic_le s (fun i => ‖c i‖)
      (fun i j => ‖inner ℂ (v i) (v j)‖) (fun _ _ _ _ => norm_nonneg _)
      (fun i _ j _ => by rw [←inner_conj_symm,Complex.norm_conj])

theorem gram_large_sieve {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (s : Finset ι) (v : ι→E) {B : ℝ} (hB : 0≤B)
    (hrows : ∀ i∈s,(∑ j∈s,‖inner ℂ (v i) (v j)‖)≤B) (x : E) :
    (∑ i∈s,‖inner ℂ (v i) x‖^2)≤B*‖x‖^2 := by
  let c : ι→ℂ := fun i => inner ℂ (v i) x
  let y : E := ∑ i∈s,c i • v i
  let A : ℝ := ∑ i∈s,‖c i‖^2
  have hA : 0≤A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hy : ‖y‖^2≤B*A := by
    apply (norm_sum_smul_sq_le_gram s v c).trans
    calc
      _ ≤ ∑ i∈s,‖c i‖^2*B := Finset.sum_le_sum
        (fun i hi => mul_le_mul_of_nonneg_left (hrows i hi) (sq_nonneg _))
      _ = B*A := by rw [←Finset.sum_mul,mul_comm]
  have hxy : inner ℂ x y=(A:ℂ) := by
    simp only [y,inner_sum,inner_smul_right,A,Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    change inner ℂ (v i) x * inner ℂ x (v i)=_
    rw [←inner_conj_symm x (v i)]
    simpa only [Complex.normSq_eq_norm_sq,c] using Complex.mul_conj (inner ℂ (v i) x)
  have hn := norm_inner_le_norm (𝕜:=ℂ) x y
  rw [hxy,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hA] at hn
  have hn2 : A^2≤‖x‖^2*‖y‖^2 := by
    nlinarith [norm_nonneg x,norm_nonneg y]
  have hprod := mul_le_mul_of_nonneg_left hy (sq_nonneg ‖x‖)
  change A≤B*‖x‖^2
  by_cases hA0 : A=0
  · rw [hA0]
    exact mul_nonneg hB (sq_nonneg _)
  · apply le_of_mul_le_mul_right (a := A) ?_ (lt_of_le_of_ne hA (Ne.symm hA0))
    calc
      A*A = A^2 := by ring
      _ ≤ _ := hn2.trans hprod
      _ = (B*‖x‖^2)*A := by ring

noncomputable def bvExp (x : ℝ) : ℂ := Complex.exp (Complex.I*(2*Real.pi*x:ℝ))

@[simp] theorem bvExp_zero : bvExp 0=1 := by simp [bvExp]

@[simp] theorem norm_bvExp (x : ℝ) : ‖bvExp x‖=1 := by simp [bvExp,Complex.norm_exp]

theorem bvExp_add (x y : ℝ) : bvExp (x+y)=bvExp x*bvExp y := by
  unfold bvExp
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem conj_bvExp (x : ℝ) : conj (bvExp x)=bvExp (-x) := by
  unfold bvExp
  rw [←Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem bvExp_nat_mul (n : ℕ) (x : ℝ) : bvExp ((n:ℝ)*x)=bvExp x^n := by
  unfold bvExp
  rw [←Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem bvExp_sub_one_lower {x : ℝ} (hx : |x|≤1/2) :
    4*|x|≤‖bvExp x-1‖ := by
  rw [bvExp,Complex.norm_exp_I_mul_ofReal_sub_one]
  have hs : |Real.pi*x|≤Real.pi/2 := by
    rw [abs_mul,abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have h := Real.mul_abs_le_abs_sin hs
  rw [abs_mul,abs_of_pos Real.pi_pos] at h
  have hpi : Real.pi≠0 := ne_of_gt Real.pi_pos
  have he : 2/Real.pi*(Real.pi*|x|)=2*|x| := by field_simp
  rw [he] at h
  have hid : 2*Real.pi*x/2=Real.pi*x := by ring
  rw [hid,Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith

theorem exponential_sum_bound (N : ℕ) {x : ℝ} (hx : |x|≤1/2) (hx0 : x≠0) :
    ‖∑ n∈Finset.range N,bvExp ((n:ℝ)*x)‖≤1/(2*|x|) := by
  have ha : 0 < |x| := abs_pos.mpr hx0
  have hden := bvExp_sub_one_lower hx
  have hn : 0<‖bvExp x-1‖ := lt_of_lt_of_le (by positivity : 0<4*|x|) hden
  have he := geom_sum_mul (bvExp x) N
  have hnorm := congrArg norm he
  rw [norm_mul] at hnorm
  have hu : ‖bvExp x^N-1‖≤2 := by
    calc
      _ ≤ ‖bvExp x^N‖+‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [norm_pow]; norm_num
  have htimes : ‖∑ n∈Finset.range N,bvExp x^n‖*(4*|x|)≤2 := by
    exact (mul_le_mul_of_nonneg_left hden (norm_nonneg _)).trans (hnorm.trans_le hu)
  simp_rw [bvExp_nat_mul]
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2*|x|)).mpr
  nlinarith

theorem reciprocal_sum_le_harmonic {ι : Type*} (s : Finset ι) (t : ι→ℝ) (D : ℕ)
    (ht : ∀ i∈s,1≤t i ∧ t i≤D)
    (hsep : ∀ i∈s,∀ j∈s,i≠j→1≤|t i-t j|) :
    (∑ i∈s,1/t i)≤(harmonic D:ℝ) := by
  classical
  let r : ι→ℕ := fun i => ⌊t i⌋₊
  have hr : ∀ i∈s,r i∈Finset.Icc 1 D := by
    intro i hi
    exact Finset.mem_Icc.mpr ⟨Nat.le_floor (by simpa using (ht i hi).1),
      Nat.floor_le_of_le (ht i hi).2⟩
  have hinj : Set.InjOn r s := by
    intro i hi j hj he
    by_contra hij
    have h := hsep i hi j hj hij
    have hil := Nat.floor_le (le_trans (by norm_num : (0:ℝ)≤1) (ht i hi).1)
    have hjl := Nat.floor_le (le_trans (by norm_num : (0:ℝ)≤1) (ht j hj).1)
    have hiu := Nat.lt_floor_add_one (t i)
    have hju := Nat.lt_floor_add_one (t j)
    change ⌊t i⌋₊=⌊t j⌋₊ at he
    rw [he] at hil hiu
    rcases le_abs.mp h with h|h <;> linarith
  calc
    _ ≤ ∑ i∈s,1/(r i:ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply one_div_le_one_div_of_le
      · exact_mod_cast (Finset.mem_Icc.mp (hr i hi)).1
      · exact Nat.floor_le (le_trans (by norm_num : (0:ℝ)≤1) (ht i hi).1)
    _ = ∑ k∈s.image r,1/(k:ℝ) := (Finset.sum_image (f := fun k : ℕ => (1:ℝ)/k) hinj).symm
    _ ≤ ∑ k∈Finset.Icc 1 D,1/(k:ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hr)
        (fun _ _ _ => by positivity)
    _ = _ := by simp [harmonic_eq_sum_Icc]

theorem reciprocal_sum_le_scaled_harmonic {ι : Type*} (s : Finset ι) (t : ι→ℝ)
    {D : ℕ} (hD : 0<D) (ht : ∀ i∈s,1/(D:ℝ)≤t i ∧ t i≤1)
    (hsep : ∀ i∈s,∀ j∈s,i≠j→1/(D:ℝ)≤|t i-t j|) :
    (∑ i∈s,1/t i)≤(D:ℝ)*(harmonic D:ℝ) := by
  have hDr : 0<(D:ℝ) := by exact_mod_cast hD
  have hh := reciprocal_sum_le_harmonic s (fun i => (D:ℝ)*t i) D
    (fun i hi => ⟨by have h := mul_le_mul_of_nonneg_left (ht i hi).1 hDr.le
                     field_simp at h
                     nlinarith,
      by nlinarith [(ht i hi).2]⟩)
    (fun i hi j hj hij => by
      rw [←mul_sub,abs_mul,abs_of_pos hDr]
      have h := (div_le_iff₀ hDr).mp (hsep i hi j hj hij)
      nlinarith)
  have hm := mul_le_mul_of_nonneg_left hh hDr.le
  rw [Finset.mul_sum] at hm
  calc
    _ = ∑ i∈s,(D:ℝ)*(1/((D:ℝ)*t i)) := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp
    _ ≤ _ := hm

@[simp] theorem bvExp_int (m : ℤ) : bvExp m=1 := by
  unfold bvExp
  have he : Complex.I * ((2*Real.pi*(m:ℝ):ℝ):ℂ)=(m:ℂ)*(2*Real.pi*Complex.I) := by
    push_cast
    ring
  rw [he,Complex.exp_int_mul,Complex.exp_two_pi_mul_I,one_zpow]

theorem bvExp_sub_int (x : ℝ) (m : ℤ) : bvExp (x-m)=bvExp x := by
  rw [sub_eq_add_neg,bvExp_add]
  have h : bvExp (-(m:ℝ))=1 := by simpa using bvExp_int (-m)
  rw [h,mul_one]

noncomputable def bvCentered (x : ℝ) : ℝ := x-(⌊x+1/2⌋:ℤ)

theorem abs_bvCentered_le (x : ℝ) : |bvCentered x|≤1/2 := by
  have hl := Int.floor_le (x+1/2)
  have hu := Int.lt_floor_add_one (x+1/2)
  dsimp [bvCentered]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem bvExp_centered (x : ℝ) : bvExp (bvCentered x)=bvExp x := bvExp_sub_int _ _

theorem exponential_sum_centered (N : ℕ) (x : ℝ) :
    (∑ n∈Finset.range N,bvExp ((n:ℝ)*bvCentered x))=
      ∑ n∈Finset.range N,bvExp ((n:ℝ)*x) := by
  simp_rw [bvExp_nat_mul,bvExp_centered]

theorem centered_difference_separated {ι : Type*} (s : Finset ι) (θ : ι→ℝ) {D : ℕ}
    (hsep : ∀ i∈s,∀ j∈s,i≠j→∀ m:ℤ,1/(D:ℝ)≤|θ i-θ j-m|)
    (a : ℝ) {i j : ι} (hi : i∈s) (hj : j∈s) (hij : i≠j) :
    1/(D:ℝ)≤|bvCentered (θ i-a)-bvCentered (θ j-a)| := by
  have h := hsep i hi j hj hij (⌊θ i-a+1/2⌋-⌊θ j-a+1/2⌋)
  dsimp [bvCentered]
  convert h using 2
  push_cast
  ring

theorem exponential_kernel_row_bound {ι : Type*} (s : Finset ι) (θ : ι→ℝ)
    {D : ℕ} (hD : 0<D)
    (hsep : ∀ i∈s,∀ j∈s,i≠j→∀ m:ℤ,1/(D:ℝ)≤|θ i-θ j-m|)
    (N : ℕ) {i : ι} (hi : i∈s) :
    (∑ j∈s,‖∑ n∈Finset.range N,bvExp ((n:ℝ)*(θ j-θ i))‖)≤
      (N:ℝ)+(D:ℝ)*(harmonic D:ℝ) := by
  classical
  let t := s.erase i
  let r := fun j => bvCentered (θ j-θ i)
  have hDr : 0<(D:ℝ) := by exact_mod_cast hD
  have hr : ∀ j∈t,1/(D:ℝ)≤|r j| := by
    intro j hj
    rcases Finset.mem_erase.mp hj with ⟨hji,hjs⟩
    exact hsep j hjs i hi hji ⌊θ j-θ i+1/2⌋
  have hn : ∀ j∈t,r j≠0 := by
    intro j hj hj0
    have h := hr j hj
    rw [hj0,abs_zero] at h
    exact (not_le_of_gt (one_div_pos.mpr hDr)) h
  have hpair : ∀ j∈t,∀ k∈t,j≠k→1/(D:ℝ)≤|r j-r k| := by
    intro j hj k hk hjk
    exact centered_difference_separated s θ hsep (θ i)
      (Finset.mem_of_mem_erase hj) (Finset.mem_of_mem_erase hk) hjk
  have hhalf : ∀ b:Bool,
      (∑ j∈t.filter (fun j => decide (0≤r j)=b),1/|r j|)≤(D:ℝ)*(harmonic D:ℝ) := by
    intro b
    apply reciprocal_sum_le_scaled_harmonic _ _ hD
    · intro j hj
      exact ⟨hr j ((Finset.mem_filter.mp hj).1),(abs_bvCentered_le _).trans (by norm_num)⟩
    · intro j hj k hk hjk
      have h := hpair j ((Finset.mem_filter.mp hj).1) k ((Finset.mem_filter.mp hk).1) hjk
      have hjb := (Finset.mem_filter.mp hj).2
      have hkb := (Finset.mem_filter.mp hk).2
      cases b <;> simp only [decide_eq_false_iff_not,decide_eq_true_eq,not_le] at hjb hkb
      · simpa only [abs_of_neg hjb,abs_of_neg hkb,neg_sub_neg,abs_sub_comm] using h
      · simpa only [abs_of_nonneg hjb,abs_of_nonneg hkb] using h
  have hrec : (∑ j∈t,1/|r j|)≤2*(D:ℝ)*(harmonic D:ℝ) := by
    have hp := hhalf true
    have hm := hhalf false
    simp only [decide_eq_true_eq,decide_eq_false_iff_not] at hp hm
    have he := Finset.sum_filter_add_sum_filter_not t (fun j => 0≤r j) (fun j => 1/|r j|)
    linarith
  have hoff : (∑ j∈t,‖∑ n∈Finset.range N,bvExp ((n:ℝ)*(θ j-θ i))‖)≤
      (D:ℝ)*(harmonic D:ℝ) := by
    calc
      _ ≤ ∑ j∈t,1/(2*|r j|) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [←exponential_sum_centered]
        exact exponential_sum_bound N (abs_bvCentered_le _) (hn j hj)
      _ = (∑ j∈t,1/|r j|)/2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ _ := by linarith
  rw [←Finset.sum_erase_add _ _ hi]
  have hd : ‖∑ n∈Finset.range N,bvExp ((n:ℝ)*(θ i-θ i))‖=(N:ℝ) := by simp
  rw [hd]
  linarith

noncomputable def bvExponentialVector (N : ℕ) (θ : ℝ) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun n => bvExp (-((n:ℕ):ℝ)*θ))

theorem inner_bvExponentialVector (N : ℕ) (θ η : ℝ) :
    inner ℂ (bvExponentialVector N θ) (bvExponentialVector N η)=
      ∑ n∈Finset.range N,bvExp ((n:ℝ)*(θ-η)) := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,bvExponentialVector]
  simp_rw [mul_comm (bvExp _)]
  simp_rw [conj_bvExp,←bvExp_add]
  have he : ∀ n:Fin N,-(-((n:ℕ):ℝ)*θ)+(-((n:ℕ):ℝ)*η)=((n:ℕ):ℝ)*(θ-η) := by
    intro n
    ring
  simp_rw [he]
  exact Fin.sum_univ_eq_sum_range (fun n : ℕ => bvExp ((n:ℝ)*(θ-η))) N

theorem inner_bvExponentialVector_coefficients (N : ℕ) (θ : ℝ) (a : Fin N→ℂ) :
    inner ℂ (bvExponentialVector N θ) (WithLp.toLp 2 a)=
      ∑ n:Fin N,a n*bvExp (((n:ℕ):ℝ)*θ) := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,bvExponentialVector]
  apply Finset.sum_congr rfl
  intro n _
  rw [conj_bvExp]
  congr 2
  ring

theorem additive_large_sieve {ι : Type*} (s : Finset ι) (θ : ι→ℝ)
    {D : ℕ} (hD : 0<D)
    (hsep : ∀ i∈s,∀ j∈s,i≠j→∀ m:ℤ,1/(D:ℝ)≤|θ i-θ j-m|)
    (N : ℕ) (a : Fin N→ℂ) :
    (∑ i∈s,‖∑ n:Fin N,a n*bvExp (((n:ℕ):ℝ)*θ i)‖^2)≤
      ((N:ℝ)+(D:ℝ)*(harmonic D:ℝ))*(∑ n:Fin N,‖a n‖^2) := by
  have hH : 0≤(harmonic D:ℝ) := by
    rw [harmonic_eq_sum_Icc,Rat.cast_sum]
    exact Finset.sum_nonneg (fun _ _ => by simp only [Rat.cast_inv,Rat.cast_natCast]; positivity)
  have hB : 0≤(N:ℝ)+(D:ℝ)*(harmonic D:ℝ) := by positivity
  have hr : ∀ i∈s,(∑ j∈s,‖inner ℂ (bvExponentialVector N (θ i))
      (bvExponentialVector N (θ j))‖)≤(N:ℝ)+(D:ℝ)*(harmonic D:ℝ) := by
    intro i hi
    simp_rw [inner_bvExponentialVector]
    have hh := exponential_kernel_row_bound s (fun i => -θ i) hD
      (fun j hj k hk hjk m => by
        have h := hsep j hj k hk hjk (-m)
        have he : -θ j- -θ k-(m:ℝ)=-(θ j-θ k-(-m:ℤ)) := by
          push_cast
          ring
        rw [he,abs_neg]
        exact h) N hi
    convert hh using 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    ring
  have h := gram_large_sieve s (fun i => bvExponentialVector N (θ i)) hB hr (WithLp.toLp 2 a)
  simpa only [inner_bvExponentialVector_coefficients,EuclideanSpace.norm_sq_eq,WithLp.ofLp_toLp] using h

theorem rat_abs_lower (r : ℚ) (hr : r≠0) : 1/(r.den:ℝ)≤|(r:ℝ)| := by
  have hn : r.num≠0 := fun h => hr (Rat.zero_of_num_zero h)
  have ha : (1:ℝ)≤|(r.num:ℝ)| := by
    exact_mod_cast Int.one_le_abs hn
  rw [Rat.cast_def,abs_div,abs_of_pos (by exact_mod_cast r.den_pos : (0:ℝ)<r.den)]
  exact div_le_div_of_nonneg_right ha (Nat.cast_nonneg _)

theorem rational_frequency_separation {r t : ℚ} {Q : ℕ}
    (hr : 0≤r ∧ r<1) (ht : 0≤t ∧ t<1) (hrt : r≠t)
    (hrQ : r.den≤Q) (htQ : t.den≤Q) (m : ℤ) :
    1/((Q^2:ℕ):ℝ)≤|(r:ℝ)-(t:ℝ)-m| := by
  have hu0 : r-t-(m:ℚ)≠0 := by
    intro he
    have hm0 : m=0 := by
      have hlo : (-1:ℚ)<(m:ℚ) := by linarith [hr.1,ht.2]
      have hup : (m:ℚ)<1 := by linarith [ht.1,hr.2]
      have h1 : (-1:ℤ) < m := by exact_mod_cast hlo
      have h2 : m<1 := by exact_mod_cast hup
      omega
    simp only [hm0,Int.cast_zero,sub_zero,sub_eq_zero] at he
    exact hrt he
  have hd : (r-t-(m:ℚ)).den≤Q^2 := by
    rw [Rat.sub_intCast_den]
    calc
      _ ≤ r.den*t.den := Nat.le_of_dvd (Nat.mul_pos r.den_pos t.den_pos) (Rat.sub_den_dvd _ _)
      _ ≤ Q*Q := Nat.mul_le_mul hrQ htQ
      _ = _ := by ring
  have hl := rat_abs_lower (r-t-(m:ℚ)) hu0
  push_cast at hl
  exact (one_div_le_one_div_of_le
    (by exact_mod_cast (r-t-(m:ℚ)).den_pos : (0:ℝ)<(r-t-(m:ℚ)).den)
    (by exact_mod_cast hd)).trans hl

theorem rational_additive_large_sieve (s : Finset ℚ) {Q : ℕ} (hQ : 0<Q)
    (hs : ∀ r∈s,0≤r ∧ r<1 ∧ r.den≤Q) (N : ℕ) (a : Fin N→ℂ) :
    (∑ r∈s,‖∑ n:Fin N,a n*bvExp (((n:ℕ):ℝ)*(r:ℝ))‖^2)≤
      ((N:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*(∑ n:Fin N,‖a n‖^2) := by
  have h := additive_large_sieve s (fun r => (r:ℝ)) (pow_pos hQ 2)
    (fun r hr t ht hrt m => rational_frequency_separation
      ⟨(hs r hr).1,(hs r hr).2.1⟩ ⟨(hs t ht).1,(hs t ht).2.1⟩ hrt
      (hs r hr).2.2 (hs t ht).2.2 m) N a
  simpa only [Nat.cast_pow] using h

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_AdditiveSieve

section File_OpenAIPrimeGaps_MultiplicativeSieve

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

theorem conj_stdAddChar {q : ℕ} [NeZero q] (a : ZMod q) :
    conj (ZMod.stdAddChar a)=ZMod.stdAddChar (-a) := by
  rw [ZMod.stdAddChar_apply,ZMod.stdAddChar_apply,AddChar.map_neg_eq_inv]
  exact Circle.coe_inv_eq_conj (ZMod.toCircle a) |>.symm

theorem conj_gaussSum_eq_dft_inverse {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    conj (gaussSum χ ZMod.stdAddChar)=ZMod.dft (χ⁻¹ : DirichletCharacter ℂ q) 1 := by
  simp only [gaussSum,map_sum,map_mul,ZMod.dft_apply,smul_eq_mul,mul_one]
  apply Finset.sum_congr rfl
  intro a _
  rw [conj_stdAddChar]
  have h : conj (χ a)=(χ⁻¹) a := MulChar.star_apply' χ a
  rw [h,mul_comm]

theorem primitive_gauss_mul_conjugate {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar*conj (gaussSum χ ZMod.stdAddChar)=(q:ℂ) := by
  have hf : ZMod.dft χ=(fun k => χ⁻¹ (-k)*gaussSum χ ZMod.stdAddChar) := by
    funext k
    exact hχ.fourierTransform_eq_inv_mul_gaussSum k
  have hh := congrFun (ZMod.dft_dft χ) (-1)
  rw [hf,ZMod.dft_mul_const,ZMod.dft_comp_neg] at hh
  change ZMod.dft (χ⁻¹ : DirichletCharacter ℂ q) (-(-1))*gaussSum χ ZMod.stdAddChar=_ at hh
  simp only [neg_neg,map_one,smul_eq_mul,mul_one] at hh
  rw [conj_gaussSum_eq_dft_inverse,mul_comm]
  exact hh

theorem primitive_gauss_norm_sq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : ‖gaussSum χ ZMod.stdAddChar‖^2=(q:ℝ) := by
  have h := primitive_gauss_mul_conjugate hχ
  rw [Complex.mul_conj,Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

noncomputable def characterUnitVector {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) :
    EuclideanSpace ℂ (DirichletCharacter ℂ q) := WithLp.toLp 2 (fun χ => χ u)

theorem conj_character_unit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (u : (ZMod q)ˣ) :
    conj (χ u)=χ (u.val⁻¹) := by
  change star (χ (u:ZMod q))=_
  rw [MulChar.star_apply',MulChar.inv_apply,Ring.inverse_unit,ZMod.inv_coe_unit]

theorem inner_characterUnitVector {q : ℕ} [NeZero q] (u v : (ZMod q)ˣ) :
    inner ℂ (characterUnitVector u) (characterUnitVector v)=if u=v then (q.totient:ℂ) else 0 := by
  classical
  simp only [PiLp.inner_apply,RCLike.inner_apply,characterUnitVector]
  simp_rw [conj_character_unit]
  have he : (∑ χ : DirichletCharacter ℂ q,χ v*χ (u.val⁻¹))=
      ∑ χ : DirichletCharacter ℂ q,χ (u.val⁻¹)*χ v := by
    apply Finset.sum_congr rfl
    intro χ _
    rw [mul_comm]
  rw [he,DirichletCharacter.sum_char_inv_mul_char_eq ℂ u.isUnit]
  simp only [Units.val_inj]

theorem character_transform_bound {q : ℕ} [NeZero q] (f : (ZMod q)ˣ→ℂ) :
    (∑ χ : DirichletCharacter ℂ q,‖∑ u : (ZMod q)ˣ, f u*χ u‖^2)≤
      (q.totient:ℝ)*(∑ u : (ZMod q)ˣ,‖f u‖^2) := by
  classical
  have hv : ∀ u : (ZMod q)ˣ,(∑ v : (ZMod q)ˣ,
      ‖inner ℂ (characterUnitVector u) (characterUnitVector v)‖)=(q.totient:ℝ) := by
    intro u
    simp only [inner_characterUnitVector]
    simp_rw [apply_ite norm]
    simp
  have h := norm_sum_smul_sq_le_gram Finset.univ (fun u : (ZMod q)ˣ => characterUnitVector u) f
  simp_rw [hv] at h
  rw [←Finset.sum_mul,mul_comm] at h
  rw [EuclideanSpace.norm_sq_eq] at h
  simpa only [WithLp.ofLp_sum,WithLp.ofLp_smul,characterUnitVector,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul] using h

noncomputable def sequenceCharacterSum {q N : ℕ} (a : Fin N→ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n:Fin N,a n*χ ((n:ℕ):ZMod q)

noncomputable def modularFourierSum {q N : ℕ} [NeZero q] (a : Fin N→ℂ) (u : ZMod q) : ℂ :=
  ∑ n:Fin N,a n*ZMod.stdAddChar (((n:ℕ):ZMod q)*u)

theorem primitive_inverse {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    (χ⁻¹).IsPrimitive := by
  change (χ⁻¹).conductor=q
  rw [DirichletCharacter.conductor_inv]
  exact hχ

theorem multiply_sum_units {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (f : ZMod q→ℂ) :
    (∑ x:ZMod q,χ x*f x)=∑ u:(ZMod q)ˣ,χ u*f u := by
  symm
  apply Fintype.sum_of_injective Units.val Units.val_injective
  · intro x hx
    have hu : ¬IsUnit x := by
      rintro ⟨u,rfl⟩
      exact hx ⟨u,rfl⟩
    rw [MulChar.map_nonunit _ hu,zero_mul]
  · intro u
    rfl

theorem primitive_character_gauss_expansion {q N : ℕ} [NeZero q]
    (a : Fin N→ℂ) {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    gaussSum (χ⁻¹) ZMod.stdAddChar*sequenceCharacterSum a χ=
      ∑ u:(ZMod q)ˣ,modularFourierSum (q:=q) a (u:ZMod q)*(χ⁻¹) u := by
  have hg (n:Fin N) := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar
    (primitive_inverse hχ) (((n:ℕ):ZMod q))
  simp only [inv_inv] at hg
  unfold sequenceCharacterSum
  rw [Finset.mul_sum]
  calc
    _ = ∑ n:Fin N,a n*gaussSum (χ⁻¹) (ZMod.stdAddChar.mulShift (((n:ℕ):ZMod q))) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [hg]
      ring
    _ = ∑ x:ZMod q,(χ⁻¹) x*modularFourierSum a x := by
      simp only [gaussSum,AddChar.mulShift_apply,Finset.mul_sum,modularFourierSum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = ∑ u:(ZMod q)ˣ,(χ⁻¹) u*modularFourierSum (q:=q) a (u:ZMod q) := multiply_sum_units _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u _
      rw [mul_comm]

theorem primitive_character_energy_le {q N : ℕ} [NeZero q] (a : Fin N→ℂ) :
    (q:ℝ)/(q.totient:ℝ)*
        (∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖sequenceCharacterSum a χ‖^2)≤
      ∑ u:(ZMod q)ˣ,‖modularFourierSum (q:=q) a (u:ZMod q)‖^2 := by
  classical
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hs : (q:ℝ)*
        (∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖sequenceCharacterSum a χ‖^2)≤
      (q.totient:ℝ)*(∑ u:(ZMod q)ˣ,‖modularFourierSum (q:=q) a (u:ZMod q)‖^2) := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ u:(ZMod q)ˣ,modularFourierSum (q:=q) a (u:ZMod q)*(χ⁻¹) u‖^2 := by
        apply Finset.sum_congr rfl
        intro χ hχ
        have hp := (Finset.mem_filter.mp hχ).2
        have h := congrArg (fun z:ℂ => ‖z‖^2) (primitive_character_gauss_expansion a hp)
        rwa [norm_mul,mul_pow,primitive_gauss_norm_sq (primitive_inverse hp)] at h
      _ ≤ ∑ χ:DirichletCharacter ℂ q,‖∑ u:(ZMod q)ˣ,modularFourierSum (q:=q) a (u:ZMod q)*(χ⁻¹) u‖^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
      _ = ∑ χ:DirichletCharacter ℂ q,‖∑ u:(ZMod q)ˣ,modularFourierSum (q:=q) a (u:ZMod q)*χ u‖^2 := by
        exact Fintype.sum_bijective (fun χ : DirichletCharacter ℂ q => χ⁻¹)
          inv_involutive.bijective _ _ (fun _ => rfl)
      _ ≤ _ := character_transform_bound _
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hφ).mpr (by simpa only [mul_comm] using hs)

noncomputable def unitFrequency {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) : ℚ := (u.val.val:ℚ)/q

theorem unitFrequency_den {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) : (unitFrequency u).den=q := by
  have hc : Nat.Coprime u.val.val q := (ZMod.isUnit_iff_coprime _ _).mp
    (by simpa only [ZMod.natCast_zmod_val] using u.isUnit)
  have he : unitFrequency u=Rat.divInt (u.val.val:ℤ) (q:ℤ) := by
    rw [Rat.divInt_eq_div]
    simp only [unitFrequency,Int.cast_natCast]
  rw [he,Rat.den_divInt]
  simp only [ite_eq_right (Int.natCast_ne_zero.mpr (NeZero.ne q)), Int.natAbs_natCast,
    Int.gcd_natCast_natCast,hc.symm.gcd_eq_one,Nat.div_one]

theorem unitFrequency_bounds {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) :
    0≤unitFrequency u ∧ unitFrequency u<1 := by
  have hq : (0:ℚ)<q := by exact_mod_cast NeZero.pos q
  exact ⟨div_nonneg (Nat.cast_nonneg _) hq.le,(div_lt_one hq).mpr (by exact_mod_cast ZMod.val_lt u.val)⟩

noncomputable def fareyFrequency {Q : ℕ} (x : Σ q:Fin Q,(ZMod (q.val+1))ˣ) : ℚ := unitFrequency x.2

theorem fareyFrequency_injective (Q : ℕ) :
    Function.Injective (fareyFrequency (Q:=Q)) := by
  rintro ⟨q,u⟩ ⟨r,v⟩ he
  have hd := congrArg Rat.den he
  simp only [fareyFrequency,unitFrequency_den] at hd
  have hqr : q=r := Fin.ext (by omega)
  subst r
  have hv : u=v := by
    apply Units.val_injective
    apply ZMod.val_injective
    change (u.val.val:ℚ)/(q.val+1:ℕ)=(v.val.val:ℚ)/(q.val+1:ℕ) at he
    have hq : ((q.val+1:ℕ):ℚ)≠0 := by positivity
    have he' := (div_left_inj' hq).mp he
    exact_mod_cast he'
  subst v
  rfl

theorem modularFourierSum_eq_bvExp {q N : ℕ} [NeZero q] (a : Fin N→ℂ) (u : (ZMod q)ˣ) :
    modularFourierSum (q:=q) a (u:ZMod q)=
      ∑ n:Fin N,a n*bvExp (((n:ℕ):ℝ)*(unitFrequency u:ℝ)) := by
  unfold modularFourierSum
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  have he : (((n:ℕ)*u.val.val:ℕ):ZMod q)=((n:ℕ):ZMod q)*(u:ZMod q) := by simp
  rw [←he]
  have hh := ZMod.stdAddChar_coe (N:=q) (((n:ℕ)*u.val.val:ℕ):ℤ)
  simp only [Int.cast_natCast] at hh
  rw [hh]
  unfold bvExp unitFrequency
  push_cast
  congr 1
  ring

theorem multiplicative_large_sieve (Q N : ℕ) (a : Fin N→ℂ) :
    (∑ q:Fin Q,((q.val+1:ℕ):ℝ)/((q.val+1).totient:ℝ)*
      (∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ (q.val+1))).filter (fun χ => χ.IsPrimitive),
        ‖sequenceCharacterSum a χ‖^2))≤
      ((N:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*(∑ n:Fin N,‖a n‖^2) := by
  classical
  by_cases hQ : Q=0
  · subst Q
    simp only [Finset.univ_eq_empty,Finset.sum_empty,Nat.cast_zero,zero_pow (by decide : 2≠0),
      zero_mul,add_zero]
    positivity
  have hQpos : 0<Q := Nat.pos_of_ne_zero hQ
  let s : Finset ℚ := Finset.univ.image (fareyFrequency (Q:=Q))
  have hs : ∀ r∈s,0≤r ∧ r<1 ∧ r.den≤Q := by
    intro r hr
    obtain ⟨⟨q,u⟩,_,rfl⟩ := Finset.mem_image.mp hr
    exact ⟨(unitFrequency_bounds u).1,(unitFrequency_bounds u).2,by
      rw [fareyFrequency,unitFrequency_den]
      omega⟩
  calc
    _ ≤ ∑ q:Fin Q,∑ u:(ZMod (q.val+1))ˣ,‖modularFourierSum (q:=q.val+1) a (u:ZMod (q.val+1))‖^2 :=
      Finset.sum_le_sum (fun _ _ => primitive_character_energy_le a)
    _ = ∑ r∈s,‖∑ n:Fin N,a n*bvExp (((n:ℕ):ℝ)*(r:ℝ))‖^2 := by
      dsimp only [s]
      rw [Finset.sum_image (fareyFrequency_injective Q).injOn,Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro u _
      rw [modularFourierSum_eq_bvExp]
      rfl
    _ ≤ _ := rational_additive_large_sieve s hQpos hs N a

theorem weighted_sum_mul_sq_le {ι : Type*} (s : Finset ι) (w f g : ι→ℝ)
    (hw : ∀ i∈s,0≤w i) :
    (∑ i∈s,w i*(f i*g i))^2≤(∑ i∈s,w i*f i^2)*(∑ i∈s,w i*g i^2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i hi
    exact mul_nonneg (hw i hi) (sq_nonneg _)
  · intro i hi
    exact mul_nonneg (hw i hi) (sq_nonneg _)
  · intro i _
    exact le_of_eq (by ring)

noncomputable def primitiveCharacterMean (Q : ℕ)
    (f : (q:Fin Q)→DirichletCharacter ℂ (q.val+1)→ℝ) : ℝ :=
  ∑ q:Fin Q,((q.val+1:ℕ):ℝ)/((q.val+1).totient:ℝ)*
    ∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ (q.val+1))).filter (fun χ=>χ.IsPrimitive),f q χ

theorem primitiveCharacterMean_nonneg {Q : ℕ}
    (f : (q:Fin Q)→DirichletCharacter ℂ (q.val+1)→ℝ)
    (hf : ∀ q χ,0≤f q χ) : 0≤primitiveCharacterMean Q f := by
  apply Finset.sum_nonneg
  intro q _
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun χ _ => hf q χ))

theorem primitiveCharacterMean_cauchy {Q : ℕ}
    (f g : (q:Fin Q)→DirichletCharacter ℂ (q.val+1)→ℝ) :
    (primitiveCharacterMean Q (fun q χ=>f q χ*g q χ))^2≤
      primitiveCharacterMean Q (fun q χ=>f q χ^2)*
      primitiveCharacterMean Q (fun q χ=>g q χ^2) := by
  classical
  let w : (Σ q:Fin Q,DirichletCharacter ℂ (q.val+1))→ℝ := fun x =>
    if x.2.IsPrimitive then ((x.1.val+1:ℕ):ℝ)/((x.1.val+1).totient:ℝ) else 0
  have hw (x : Σ q:Fin Q,DirichletCharacter ℂ (q.val+1)) : 0≤w x := by
    dsimp [w]
    split <;> positivity
  have hsum (a : (q:Fin Q)→DirichletCharacter ℂ (q.val+1)→ℝ) :
      (∑ x : Σ q:Fin Q,DirichletCharacter ℂ (q.val+1),w x*a x.1 x.2)=
        primitiveCharacterMean Q a := by
    rw [Fintype.sum_sigma]
    unfold primitiveCharacterMean
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.mul_sum,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro χ _
    dsimp [w]
    split <;> simp_all
  have h:=weighted_sum_mul_sq_le Finset.univ w (fun x=>f x.1 x.2) (fun x=>g x.1 x.2)
    (fun x _ => hw x)
  rw [←hsum (fun q χ=>f q χ*g q χ),←hsum (fun q χ=>f q χ^2),
    ←hsum (fun q χ=>g q χ^2)]
  exact h

theorem bilinear_multiplicative_large_sieve (Q M N : ℕ) (a : Fin M→ℂ) (b : Fin N→ℂ) :
    (primitiveCharacterMean Q (fun _ χ=>‖sequenceCharacterSum a χ*sequenceCharacterSum b χ‖))^2≤
      (((M:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*(∑ m:Fin M,‖a m‖^2))*
      (((N:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*(∑ n:Fin N,‖b n‖^2)) := by
  have h:=primitiveCharacterMean_cauchy (Q:=Q)
    (fun _ χ=>‖sequenceCharacterSum a χ‖) (fun _ χ=>‖sequenceCharacterSum b χ‖)
  simp only [norm_mul]
  exact h.trans (mul_le_mul (multiplicative_large_sieve Q M a) (multiplicative_large_sieve Q N b)
    (primitiveCharacterMean_nonneg _ (fun _ _ => sq_nonneg _))
    ((primitiveCharacterMean_nonneg _ (fun _ _ => sq_nonneg _)).trans (multiplicative_large_sieve Q M a)))

theorem sequenceCharacterSum_mul {q M N : ℕ} (a : Fin M→ℂ) (b : Fin N→ℂ)
    (χ : DirichletCharacter ℂ q) :
    sequenceCharacterSum a χ*sequenceCharacterSum b χ=
      ∑ m:Fin M,∑ n:Fin N,a m*b n*χ (((m:ℕ)*(n:ℕ):ℕ):ZMod q) := by
  unfold sequenceCharacterSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [Nat.cast_mul,map_mul]
  ring

theorem exponential_kernel_offdiagonal_bound {ι : Type*} [DecidableEq ι] (s : Finset ι) (θ : ι→ℝ)
    {D : ℕ} (hD : 0<D)
    (hsep : ∀ i∈s,∀ j∈s,i≠j→∀ m:ℤ,1/(D:ℝ)≤|θ i-θ j-m|)
    (N : ℕ) {i : ι} (hi : i∈s) :
    (∑ j∈s.erase i,‖∑ n∈Finset.range N,bvExp ((n:ℝ)*(θ j-θ i))‖)≤
      (D:ℝ)*(harmonic D:ℝ) := by
  have h:=exponential_kernel_row_bound s θ hD hsep N hi
  rw [←Finset.sum_erase_add _ _ hi] at h
  have hd : ‖∑ n∈Finset.range N,bvExp ((n:ℝ)*(θ i-θ i))‖=(N:ℝ) := by simp
  rw [hd] at h
  linarith

theorem residue_frequency_separation {q : ℕ} [NeZero q] {a b : ZMod q}
    (hab : a≠b) (m : ℤ) :
    1/(q:ℝ)≤|(a.val:ℝ)/q-(b.val:ℝ)/q-m| := by
  have hz : (a.val:ℤ)-(b.val:ℤ)-m*(q:ℤ)≠0 := by
    intro he
    have h:=congrArg (fun t:ℤ => (t:ZMod q)) he
    simp only [Int.cast_sub,Int.cast_natCast,Int.cast_mul,ZMod.natCast_self,mul_zero,
      sub_zero,Int.cast_zero,ZMod.natCast_zmod_val] at h
    exact hab (sub_eq_zero.mp h)
  have hnum : (1:ℝ)≤|(((a.val:ℤ)-(b.val:ℤ)-m*(q:ℤ)):ℝ)| := by
    exact_mod_cast Int.one_le_abs hz
  have hq : (0:ℝ)<q := by exact_mod_cast NeZero.pos q
  have he : (a.val:ℝ)/q-(b.val:ℝ)/q-m=
      ((((a.val:ℤ)-(b.val:ℤ)-m*(q:ℤ)):ℤ):ℝ)/(q:ℝ) := by
    push_cast
    field_simp
  rw [he,abs_div,abs_of_pos hq]
  simpa only [Int.cast_sub,Int.cast_mul,Int.cast_natCast] using
    div_le_div_of_nonneg_right hnum hq.le

theorem modularFourierSum_one {q N : ℕ} [NeZero q] (u : ZMod q) :
    modularFourierSum (q:=q) (fun _:Fin N=>1) u=
      ∑ n∈Finset.range N,bvExp ((n:ℝ)*((u.val:ℝ)/q)) := by
  unfold modularFourierSum
  rw [←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n _
  rw [one_mul]
  have he : (((n:ℕ)*u.val:ℕ):ZMod q)=((n:ℕ):ZMod q)*u := by simp
  rw [←he]
  have hh:=ZMod.stdAddChar_coe (N:=q) (((n:ℕ)*u.val:ℕ):ℤ)
  simp only [Int.cast_natCast] at hh
  rw [hh]
  unfold bvExp
  push_cast
  congr 1
  ring

theorem primitive_polya_vinogradov {q : ℕ} (hq : 1<q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (N : ℕ) :
    ‖∑ n:Fin N,χ ((n:ℕ):ZMod q)‖≤Real.sqrt q*(harmonic q:ℝ) := by
  classical
  let : NeZero q := ⟨by omega⟩
  let : Fact (1<q) := ⟨hq⟩
  let θ : ZMod q→ℝ := fun x=>(x.val:ℝ)/q
  let f : ZMod q→ℝ := fun u=>‖∑ n∈Finset.range N,bvExp ((n:ℝ)*θ u)‖
  have hr : (∑ u∈(Finset.univ : Finset (ZMod q)).erase 0,f u)≤(q:ℝ)*(harmonic q:ℝ) := by
    have h:=exponential_kernel_offdiagonal_bound Finset.univ θ (by omega : 0<q)
      (fun _ _ _ _ hne m => residue_frequency_separation hne m) N (Finset.mem_univ (0:ZMod q))
    simpa only [θ,ZMod.val_zero,Nat.cast_zero,zero_div,sub_zero,f] using h
  have hu : Finset.univ.image (fun u:(ZMod q)ˣ=>(u:ZMod q))⊆(Finset.univ : Finset (ZMod q)).erase 0 := by
    intro x hx
    obtain ⟨u,_,rfl⟩:=Finset.mem_image.mp hx
    exact Finset.mem_erase.mpr ⟨Units.ne_zero u,Finset.mem_univ _⟩
  have hg:=primitive_character_gauss_expansion (fun _:Fin N=>1) hχ
  have hnorm : ‖gaussSum (χ⁻¹) ZMod.stdAddChar‖*
      ‖∑ n:Fin N,χ ((n:ℕ):ZMod q)‖≤(q:ℝ)*(harmonic q:ℝ) := by
    calc
      _ = ‖∑ u:(ZMod q)ˣ,modularFourierSum (q:=q) (fun _:Fin N=>1) (u:ZMod q)*(χ⁻¹) u‖ := by
        simpa only [norm_mul,sequenceCharacterSum,one_mul] using congrArg norm hg
      _ ≤ ∑ u:(ZMod q)ˣ,‖modularFourierSum (q:=q) (fun _:Fin N=>1) (u:ZMod q)*(χ⁻¹) u‖ := norm_sum_le _ _
      _ ≤ ∑ u:(ZMod q)ˣ,f (u:ZMod q) := by
        apply Finset.sum_le_sum
        intro u _
        rw [norm_mul,modularFourierSum_one]
        exact mul_le_of_le_one_right (norm_nonneg _) ((χ⁻¹).norm_le_one _)
      _ = ∑ x∈Finset.univ.image (fun u:(ZMod q)ˣ=>(u:ZMod q)),f x := by
        rw [Finset.sum_image Units.val_injective.injOn]
      _ ≤ ∑ x∈(Finset.univ : Finset (ZMod q)).erase 0,f x :=
        Finset.sum_le_sum_of_subset_of_nonneg hu (fun _ _ _ => norm_nonneg _)
      _ ≤ _ := hr
  have hgn : ‖gaussSum (χ⁻¹) ZMod.stdAddChar‖=Real.sqrt q := by
    have hs:=primitive_gauss_norm_sq (primitive_inverse hχ)
    rw [←hs,Real.sqrt_sq (norm_nonneg _)]
  rw [hgn] at hnorm
  have hsq : (Real.sqrt (q:ℝ))^2=(q:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hpos : 0<Real.sqrt (q:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0<q by omega))
  have he : (q:ℝ)*(harmonic q:ℝ)=Real.sqrt q*(Real.sqrt q*(harmonic q:ℝ)) := by
    calc
      _ = (Real.sqrt (q:ℝ))^2*(harmonic q:ℝ) := by rw [hsq]
      _ = _ := by ring
  rw [he] at hnorm
  exact (mul_le_mul_iff_right₀ hpos).mp hnorm

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_MultiplicativeSieve

section File_OpenAIPrimeGaps_VaughanIdentity

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

theorem monotone_weighted_prefix_bound (g : ℕ→ℂ) (w : ℕ→ℝ) (hw : Monotone w)
    (hw0 : 0≤w 0) {B : ℝ} (hB : 0≤B) (N : ℕ)
    (hg : ∀ n≤N,‖∑ i∈Finset.range n,g i‖≤B) :
    ‖∑ i∈Finset.range N,(w i:ℂ)*g i‖≤2*w (N-1)*B := by
  have hwpos (n : ℕ) : 0≤w n := hw0.trans (hw (Nat.zero_le n))
  have hd (n : ℕ) : 0≤w (n+1)-w n := sub_nonneg.mpr (hw (by omega))
  have he:=Finset.sum_range_by_parts w g N
  simp only [Complex.real_smul] at he
  rw [he]
  calc
    _ ≤ ‖(w (N-1):ℂ)*(∑ i∈Finset.range N,g i)‖+
        ‖∑ i∈Finset.range (N-1),((w (i+1)-w i:ℝ):ℂ)*(∑ j∈Finset.range (i+1),g j)‖ := norm_sub_le _ _
    _ ≤ w (N-1)*B+(∑ i∈Finset.range (N-1),(w (i+1)-w i)*B) := by
      apply add_le_add
      · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hwpos _)]
        exact mul_le_mul_of_nonneg_left (hg N le_rfl) (hwpos _)
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
        intro i hi
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hd _)]
        exact mul_le_mul_of_nonneg_left (hg (i+1) (by have h:=Finset.mem_range.mp hi; omega)) (hd _)
    _ = w (N-1)*B+(w (N-1)-w 0)*B := by
      rw [←Finset.sum_mul,Finset.sum_range_sub]
    _ ≤ _ := by nlinarith

theorem log_nat_monotone : Monotone (fun n:ℕ=>Real.log n) := by
  intro n m hnm
  by_cases hn : n=0
  · subst n
    simp only [Nat.cast_zero,Real.log_zero]
    by_cases hm : m=0
    · simp [hm]
    · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm)
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn) (by exact_mod_cast hnm)

theorem primitive_log_character_bound {q : ℕ} (hq : 1<q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (N : ℕ) :
    ‖∑ n∈Finset.range N,(Real.log n:ℂ)*χ (n:ZMod q)‖≤
      2*Real.log N*(Real.sqrt q*(harmonic q:ℝ)) := by
  have hH : 0≤(harmonic q:ℝ) := by exact_mod_cast (harmonic_pos (by omega : q≠0)).le
  have hB : 0≤Real.sqrt q*(harmonic q:ℝ) := mul_nonneg (Real.sqrt_nonneg _) hH
  have h:=monotone_weighted_prefix_bound (fun n=>χ (n:ZMod q)) (fun n:ℕ=>Real.log n)
    log_nat_monotone (by simp) hB N (fun n _ => by
      rw [←Fin.sum_univ_eq_sum_range (fun i:ℕ=>χ (i:ZMod q)) n]
      exact primitive_polya_vinogradov hq hχ n)
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (log_nat_monotone (Nat.sub_le N 1)) (by norm_num)) hB)

theorem primitive_typeI_log_bound {q : ℕ} (hq : 1<q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (X D : ℕ) (a : ℕ→ℂ) :
    ‖∑ d∈Finset.Icc 1 D,a d*χ (d:ZMod q)*
      (∑ n∈Finset.range (X/d+1),(Real.log n:ℂ)*χ (n:ZMod q))‖≤
      (∑ d∈Finset.Icc 1 D,‖a d‖)*
        (2*Real.log (X+1:ℕ)*(Real.sqrt q*(harmonic q:ℝ))) := by
  calc
    _ ≤ ∑ d∈Finset.Icc 1 D,‖a d*χ (d:ZMod q)*
      (∑ n∈Finset.range (X/d+1),(Real.log n:ℂ)*χ (n:ZMod q))‖ := norm_sum_le _ _
    _ ≤ ∑ d∈Finset.Icc 1 D,‖a d‖*(2*Real.log (X+1:ℕ)*(Real.sqrt q*(harmonic q:ℝ))) := by
      apply Finset.sum_le_sum
      intro d _
      rw [norm_mul,norm_mul]
      apply mul_le_mul
      · exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)
      · exact (primitive_log_character_bound hq hχ _).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (log_nat_monotone (Nat.add_le_add_right (Nat.div_le_self X d) 1)) (by norm_num))
            (mul_nonneg (Real.sqrt_nonneg _) (by exact_mod_cast (harmonic_pos (by omega : q≠0)).le)))
      · exact norm_nonneg _
      · exact norm_nonneg _
    _ = _ := by rw [Finset.sum_mul]

theorem primitive_typeI_bound {q : ℕ} (hq : 1<q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (X D : ℕ) (a : ℕ→ℂ) :
    ‖∑ d∈Finset.Icc 1 D,a d*χ (d:ZMod q)*
      (∑ n∈Finset.range (X/d+1),χ (n:ZMod q))‖≤
      (∑ d∈Finset.Icc 1 D,‖a d‖)*(Real.sqrt q*(harmonic q:ℝ)) := by
  calc
    _ ≤ ∑ d∈Finset.Icc 1 D,‖a d*χ (d:ZMod q)*
      (∑ n∈Finset.range (X/d+1),χ (n:ZMod q))‖ := norm_sum_le _ _
    _ ≤ ∑ d∈Finset.Icc 1 D,‖a d‖*(Real.sqrt q*(harmonic q:ℝ)) := by
      apply Finset.sum_le_sum
      intro d _
      rw [norm_mul,norm_mul]
      apply mul_le_mul
      · exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)
      · rw [←Fin.sum_univ_eq_sum_range (fun i:ℕ=>χ (i:ZMod q)) (X/d+1)]
        exact primitive_polya_vinogradov hq hχ (X/d+1)
      · exact norm_nonneg _
      · exact norm_nonneg _
    _ = _ := by rw [Finset.sum_mul]

noncomputable def sequenceSize {N : ℕ} (a : Fin N→ℂ) : ℝ :=
  Real.sqrt (∑ n:Fin N,‖a n‖^2)

theorem sequenceSize_nonneg {N : ℕ} (a : Fin N→ℂ) : 0 ≤ sequenceSize a := Real.sqrt_nonneg _

theorem sequenceSize_sq {N : ℕ} (a : Fin N→ℂ) :
    sequenceSize a^2=∑ n:Fin N,‖a n‖^2 := Real.sq_sqrt (Finset.sum_nonneg (fun _ _=>sq_nonneg _))

noncomputable def sequenceMask {N : ℕ} (p : Fin N→Prop) (a : Fin N→ℂ) : Fin N→ℂ :=
  fun n=>if p n then a n else 0

theorem sequenceMask_size_le {N : ℕ} (p : Fin N→Prop) (a : Fin N→ℂ) :
    sequenceSize (sequenceMask p a) ≤ sequenceSize a := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro n _
  dsimp [sequenceMask]
  split <;> simp

theorem sequenceMask_size_partition {N : ℕ} (p : Fin N→Prop) (a : Fin N→ℂ) :
    sequenceSize (sequenceMask p a)^2+sequenceSize (sequenceMask (fun n=>¬p n) a)^2=
      sequenceSize a^2 := by
  rw [sequenceSize_sq,sequenceSize_sq,sequenceSize_sq,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h:p n <;> simp [sequenceMask,h]

theorem sequenceMask_cauchy {M N : ℕ} (p : Fin M→Prop) (r : Fin N→Prop)
    (a : Fin M→ℂ) (b : Fin N→ℂ) :
    sequenceSize (sequenceMask p a)*sequenceSize (sequenceMask r b)+
      sequenceSize (sequenceMask (fun m=>¬p m) a)*sequenceSize (sequenceMask (fun n=>¬r n) b) ≤
      sequenceSize a*sequenceSize b := by
  have h:=Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Bool)
    (fun z=>if z then sequenceSize (sequenceMask p a) else sequenceSize (sequenceMask (fun m=>¬p m) a))
    (fun z=>if z then sequenceSize (sequenceMask r b) else sequenceSize (sequenceMask (fun n=>¬r n) b))
  simp at h
  rw [sequenceMask_size_partition,sequenceMask_size_partition,←mul_pow] at h
  exact (sq_le_sq₀ (add_nonneg (mul_nonneg (sequenceSize_nonneg _) (sequenceSize_nonneg _))
    (mul_nonneg (sequenceSize_nonneg _) (sequenceSize_nonneg _))) (mul_nonneg (sequenceSize_nonneg a) (sequenceSize_nonneg b))).mp h

noncomputable def sieveBilinearConstant (Q M N : ℕ) : ℝ :=
  Real.sqrt ((M:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*
    Real.sqrt ((N:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))

theorem sieveBilinearConstant_nonneg (Q M N : ℕ) : 0 ≤ sieveBilinearConstant Q M N := by
  unfold sieveBilinearConstant
  positivity

theorem bilinear_primitive_mean_le (Q M N : ℕ) (a : Fin M→ℂ) (b : Fin N→ℂ) :
    primitiveCharacterMean Q (fun _ χ=>‖sequenceCharacterSum a χ*sequenceCharacterSum b χ‖) ≤
      sieveBilinearConstant Q M N*sequenceSize a*sequenceSize b := by
  have h:=bilinear_multiplicative_large_sieve Q M N a b
  have hH : 0 ≤ (harmonic (Q^2):ℝ) := by
    by_cases hh:Q=0
    · simp [hh]
    · exact_mod_cast (harmonic_pos (pow_ne_zero 2 hh)).le
  have hM : 0 ≤ (M:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ) := by positivity
  have hN : 0 ≤ (N:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ) := by positivity
  have he : (sieveBilinearConstant Q M N*sequenceSize a*sequenceSize b)^2=
      (((M:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*(∑ m:Fin M,‖a m‖^2))*
      (((N:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*(∑ n:Fin N,‖b n‖^2)) := by
    rw [mul_pow,mul_pow,sequenceSize_sq,sequenceSize_sq]
    unfold sieveBilinearConstant
    rw [mul_pow,Real.sq_sqrt hM,Real.sq_sqrt hN]
    ring
  rw [←he] at h
  exact (sq_le_sq₀ (primitiveCharacterMean_nonneg _ (fun _ _=>norm_nonneg _))
    (mul_nonneg (mul_nonneg (sieveBilinearConstant_nonneg _ _ _) (sequenceSize_nonneg _))
      (sequenceSize_nonneg _))).mp h

theorem primitiveCharacterMean_mono {Q : ℕ}
    {f g : (q:Fin Q)→DirichletCharacter ℂ (q.val+1)→ℝ}
    (h : ∀ q χ,f q χ ≤ g q χ) : primitiveCharacterMean Q f ≤ primitiveCharacterMean Q g := by
  apply Finset.sum_le_sum
  intro q _
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _=>h q χ)) (by positivity)

theorem primitiveCharacterMean_add {Q : ℕ}
    (f g : (q:Fin Q)→DirichletCharacter ℂ (q.val+1)→ℝ) :
    primitiveCharacterMean Q (fun q χ=>f q χ+g q χ)=
      primitiveCharacterMean Q f+primitiveCharacterMean Q g := by
  simp only [primitiveCharacterMean,Finset.sum_add_distrib,mul_add]

noncomputable def triangularCharacterSum {q M N : ℕ} (a : Fin M→ℂ) (b : Fin N→ℂ)
    (t : Fin M→ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ m:Fin M,∑ n:Fin N,if n.val<t m then a m*b n*χ (m.val:ZMod q)*χ (n.val:ZMod q) else 0

theorem triangularCharacterSum_split {q M N : ℕ} (a : Fin M→ℂ) (b : Fin N→ℂ)
    (t : Fin M→ℕ) (χ : DirichletCharacter ℂ q) (H : ℕ) :
    triangularCharacterSum a b t χ=
      triangularCharacterSum (sequenceMask (fun m=>t m ≤ H) a) (sequenceMask (fun n=>n.val<H) b) t χ+
      sequenceCharacterSum (sequenceMask (fun m=>¬t m ≤ H) a) χ*
        sequenceCharacterSum (sequenceMask (fun n=>n.val<H) b) χ+
      triangularCharacterSum (sequenceMask (fun m=>¬t m ≤ H) a) (sequenceMask (fun n=>¬n.val<H) b) t χ := by
  unfold triangularCharacterSum sequenceCharacterSum
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  by_cases hm:t m ≤ H <;> by_cases hn:n.val<H <;> by_cases ht:n.val<t m <;>
    simp [sequenceMask,hm,hn,ht] <;> (try omega) ; ring

theorem triangularCharacterSum_single {q M N L : ℕ} (a : Fin M→ℂ) (b : Fin N→ℂ)
    (t : Fin M→ℕ) (χ : DirichletCharacter ℂ q) (hb : ∀ n,b n≠0→n.val=L) :
    triangularCharacterSum a b t χ=
      sequenceCharacterSum (sequenceMask (fun m=>L<t m) a) χ*sequenceCharacterSum b χ := by
  unfold triangularCharacterSum sequenceCharacterSum
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn:b n=0
  · simp [hn,sequenceMask]
  · have he:=hb n hn
    by_cases ht:L<t m <;> simp [sequenceMask,he,ht] ; ring

theorem triangular_primitive_mean_dyadic (Q M N k L : ℕ) (a : Fin M→ℂ) (b : Fin N→ℂ)
    (t : Fin M→ℕ) (hb : ∀ n,b n≠0→L ≤ n.val ∧ n.val<L+2^k) :
    primitiveCharacterMean Q (fun _ χ=>‖triangularCharacterSum a b t χ‖) ≤
      ((k:ℝ)+1)*sieveBilinearConstant Q M N*sequenceSize a*sequenceSize b := by
  induction k generalizing L a b with
  | zero =>
    have he (q:Fin Q) (χ : DirichletCharacter ℂ (q.val+1)) :=
      triangularCharacterSum_single a b t χ (fun n hn=>by have h:=hb n hn; simpa using (by omega : n.val=L))
    simp only [he,Nat.cast_zero,zero_add,one_mul]
    exact (bilinear_primitive_mean_le Q M N _ _).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sequenceMask_size_le _ _) (sieveBilinearConstant_nonneg _ _ _))
        (sequenceSize_nonneg _))
  | succ k ih =>
    let H:=L+2^k
    let p : Fin M→Prop := fun m=>t m ≤ H
    let r : Fin N→Prop := fun n=>n.val<H
    let a₀:=sequenceMask p a
    let a₁:=sequenceMask (fun m=>¬p m) a
    let b₀:=sequenceMask r b
    let b₁:=sequenceMask (fun n=>¬r n) b
    have hb₀ : ∀ n,b₀ n≠0→L ≤ n.val ∧ n.val<L+2^k := by
      intro n hn
      have hn' : b n≠0 ∧ n.val<H := by
        dsimp [b₀,sequenceMask,r] at hn
        split at hn <;> simp_all
      exact ⟨(hb n hn'.1).1,hn'.2⟩
    have hb₁ : ∀ n,b₁ n≠0→H ≤ n.val ∧ n.val<H+2^k := by
      intro n hn
      have hn' : b n≠0 ∧ ¬n.val<H := by
        dsimp [b₁,sequenceMask,r] at hn
        split at hn <;> simp_all
      have h:=hb n hn'.1
      simp only [pow_succ] at h
      dsimp [H]
      omega
    have hsplit := primitiveCharacterMean_mono (Q:=Q)
      (f:=fun _ χ=>‖triangularCharacterSum a b t χ‖)
      (g:=fun _ χ=>‖triangularCharacterSum a₀ b₀ t χ‖+
        ‖sequenceCharacterSum a₁ χ*sequenceCharacterSum b₀ χ‖+
        ‖triangularCharacterSum a₁ b₁ t χ‖) (fun _ χ=>by
          rw [triangularCharacterSum_split a b t χ H]
          exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _))
    rw [primitiveCharacterMean_add,primitiveCharacterMean_add] at hsplit
    have h0:=ih L a₀ b₀ hb₀
    have h1:=ih H a₁ b₁ hb₁
    have hR:=bilinear_primitive_mean_le Q M N a₁ b₀
    have hpair:=sequenceMask_cauchy p r a b
    have hcross : sequenceSize a₁*sequenceSize b₀ ≤ sequenceSize a*sequenceSize b :=
      mul_le_mul (sequenceMask_size_le _ _) (sequenceMask_size_le _ _)
        (sequenceSize_nonneg _) (sequenceSize_nonneg _)
    have hC:=sieveBilinearConstant_nonneg Q M N
    have hk : 0 ≤ (k:ℝ)+1 := by positivity
    have hp:=mul_le_mul_of_nonneg_left hpair (mul_nonneg hk hC)
    have hc:=mul_le_mul_of_nonneg_left hcross hC
    change sequenceSize a₀*sequenceSize b₀+sequenceSize a₁*sequenceSize b₁ ≤ _ at hpair
    change ((k:ℝ)+1)*sieveBilinearConstant Q M N*
      (sequenceSize a₀*sequenceSize b₀+sequenceSize a₁*sequenceSize b₁) ≤ _ at hp
    push_cast
    nlinarith only [hsplit,h0,h1,hR,hp,hc]

theorem triangular_primitive_mean_le (Q M N k : ℕ) (hk : N ≤ 2^k)
    (a : Fin M→ℂ) (b : Fin N→ℂ) (t : Fin M→ℕ) :
    primitiveCharacterMean Q (fun _ χ=>‖triangularCharacterSum a b t χ‖) ≤
      ((k:ℝ)+1)*sieveBilinearConstant Q M N*sequenceSize a*sequenceSize b := by
  apply triangular_primitive_mean_dyadic Q M N k 0 a b t
  intro n _
  exact ⟨Nat.zero_le _,by simpa only [zero_add] using n.isLt.trans_le hk⟩

theorem sum_divisorsAntidiagonal_hyperbola (X : ℕ) (F : ℕ→ℕ→ℂ) :
    (∑ n∈Finset.Icc 1 X,∑ p∈n.divisorsAntidiagonal,F p.1 p.2)=
      ∑ d∈Finset.Icc 1 X,∑ m∈Finset.Icc 1 (X/d),F d m := by
  rw [Finset.sum_sigma',Finset.sum_sigma']
  apply Finset.sum_bij (fun x _ => (⟨x.2.1,x.2.2⟩ : (d:ℕ)×ℕ))
  · rintro ⟨n,d,m⟩ hx
    obtain ⟨hn,hdm⟩:=Finset.mem_sigma.mp hx
    obtain ⟨hn1,hnX⟩:=Finset.mem_Icc.mp hn
    obtain ⟨hdm,hn0⟩:=Nat.mem_divisorsAntidiagonal.mp hdm
    dsimp only at hn1 hnX hdm hn0
    have hd : 0 < d := by
      by_contra hh
      have he : d=0 := by omega
      simp only [he,zero_mul] at hdm
      omega
    have hm : 0 < m := by
      by_contra hh
      have he : m=0 := by omega
      simp only [he,mul_zero] at hdm
      omega
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hd,by nlinarith⟩,
      Finset.mem_Icc.mpr ⟨hm,(Nat.le_div_iff_mul_le hd).mpr (by nlinarith)⟩⟩
  · rintro ⟨n,d,m⟩ hx ⟨n',d',m'⟩ hy he
    have hv:(d,m)=(d',m'):=by simpa using congrArg (fun x:(d:ℕ)×ℕ=>(x.1,x.2)) he
    have hd:d=d':=congrArg Prod.fst hv
    have hm:m=m':=congrArg Prod.snd hv
    have hn: d*m = n := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hx).2).1
    have hn': d'*m' = n' := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hy).2).1
    subst d'; subst m'
    have hnn:n=n':=hn.symm.trans hn'
    cases hnn; rfl
  · rintro ⟨d,m⟩ hy
    obtain ⟨hd,hm⟩:=Finset.mem_sigma.mp hy
    obtain ⟨hd1,hdX⟩:=Finset.mem_Icc.mp hd
    obtain ⟨hm1,hmX⟩:=Finset.mem_Icc.mp hm
    refine ⟨⟨d*m,(d,m)⟩,?_,rfl⟩
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨by nlinarith,
      by have h: m*d ≤ X:=(Nat.le_div_iff_mul_le hd1).mp hmX; nlinarith⟩,
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl,by positivity⟩⟩
  · intro x _; rfl

noncomputable def arithmeticCharacterSum {q : ℕ} (X : ℕ) (f : ArithmeticFunction ℝ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n∈Finset.Icc 1 X,(f n:ℂ)*χ (n:ZMod q)

theorem arithmeticCharacterSum_convolution {q : ℕ} (X : ℕ)
    (f g : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X (f*g) χ=
      ∑ d∈Finset.Icc 1 X,(f d:ℂ)*χ (d:ZMod q)*
        (∑ m∈Finset.Icc 1 (X/d),(g m:ℂ)*χ (m:ZMod q)) := by
  unfold arithmeticCharacterSum
  calc
    _ = ∑ n∈Finset.Icc 1 X,∑ p∈n.divisorsAntidiagonal,
        (f p.1:ℂ)*χ (p.1:ZMod q)*((g p.2:ℂ)*χ (p.2:ZMod q)) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [ArithmeticFunction.mul_apply]
      push_cast
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      have he: p.1*p.2=n := (Nat.mem_divisorsAntidiagonal.mp hp).1
      rw [←he,Nat.cast_mul,map_mul]
      ring
    _ = _ := by
      rw [sum_divisorsAntidiagonal_hyperbola X (fun d m=>(f d:ℂ)*χ (d:ZMod q)*((g m:ℂ)*χ (m:ZMod q)))]
      simp only [Finset.mul_sum,mul_assoc]

@[simp] theorem arithmeticCharacterSum_add {q : ℕ} (X : ℕ)
    (f g : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X (f+g) χ=arithmeticCharacterSum X f χ+arithmeticCharacterSum X g χ := by
  simp [arithmeticCharacterSum,ArithmeticFunction.add_apply,add_mul,Finset.sum_add_distrib]

@[simp] theorem arithmeticCharacterSum_sub {q : ℕ} (X : ℕ)
    (f g : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X (f-g) χ=arithmeticCharacterSum X f χ-arithmeticCharacterSum X g χ := by
  unfold arithmeticCharacterSum
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  change ((f n-g n:ℝ):ℂ)*χ (n:ZMod q)=_
  push_cast
  ring

theorem vaughan_character_identity {q : ℕ} (X U V : ℕ) (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ=
      arithmeticCharacterSum X (arithmeticCutoff U ArithmeticFunction.vonMangoldt) χ+
      arithmeticCharacterSum X (arithmeticCutoff V ArithmeticFunction.moebius*ArithmeticFunction.log) χ-
      arithmeticCharacterSum X (arithmeticCutoff V ArithmeticFunction.moebius*
        arithmeticCutoff U ArithmeticFunction.vonMangoldt*ArithmeticFunction.zeta) χ+
      arithmeticCharacterSum X ((ArithmeticFunction.moebius-arithmeticCutoff V ArithmeticFunction.moebius)*
        vaughanSecondCoefficient U) χ := by
  have h:=congrArg (fun f=>arithmeticCharacterSum X f χ) (vaughan_identity U V)
  simpa only [arithmeticCharacterSum_add,arithmeticCharacterSum_sub,vaughanSecondCoefficient,mul_assoc] using h

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_VaughanIdentity

section File_OpenAIPrimeGaps_VaughanBounds

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

theorem sequenceSize_le_of_norm_le {N : ℕ} (a : Fin N→ℂ) {A : ℝ}
    (hA : 0 ≤ A) (ha : ∀ n,‖a n‖ ≤ A) : sequenceSize a ≤ Real.sqrt N*A := by
  have hh : sequenceSize a^2 ≤ (N:ℝ)*A^2 := by
    rw [sequenceSize_sq]
    calc
      _ ≤ ∑ _n:Fin N,A^2 := Finset.sum_le_sum (fun n _=>pow_le_pow_left₀ (norm_nonneg _) (ha n) 2)
      _ = _ := by simp
  have hs : (Real.sqrt (N:ℝ))^2=(N:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  apply (sq_le_sq₀ (sequenceSize_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hA)).mp
  simpa only [mul_pow,hs] using hh

noncomputable def vaughanFirstSequence (V M : ℕ) : Fin M→ℂ :=
  fun m=>if V < m.val then (ArithmeticFunction.moebius m.val:ℂ) else 0

noncomputable def vaughanSecondSequence (U N : ℕ) : Fin N→ℂ :=
  fun n=>(vaughanSecondCoefficient U n.val:ℂ)

theorem vaughanFirstSequence_norm_le (V M : ℕ) (m : Fin M) :
    ‖vaughanFirstSequence V M m‖ ≤ 1 := by
  unfold vaughanFirstSequence
  split_ifs
  · rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=m.val))
  · simp

theorem vaughanFirstSequence_size_le (V M : ℕ) :
    sequenceSize (vaughanFirstSequence V M) ≤ Real.sqrt M := by
  simpa only [mul_one] using sequenceSize_le_of_norm_le (vaughanFirstSequence V M)
    zero_le_one (vaughanFirstSequence_norm_le V M)

theorem vaughanSecondSequence_norm_le (U N : ℕ) (n : Fin N) :
    ‖vaughanSecondSequence U N n‖ ≤ Real.log N := by
  rw [vaughanSecondSequence,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (vaughanSecondCoefficient_nonneg _ _)]
  exact (vaughanSecondCoefficient_le_log _ _).trans (log_nat_monotone n.isLt.le)

theorem vaughanSecondSequence_size_le (U N : ℕ) :
    sequenceSize (vaughanSecondSequence U N) ≤ Real.sqrt N*Real.log N := by
  apply sequenceSize_le_of_norm_le _ _ (vaughanSecondSequence_norm_le U N)
  simpa using log_nat_monotone (Nat.zero_le N)

theorem vaughan_typeII_block_mean (Q X U V M N k : ℕ) (hk : N ≤ 2^k)
    (p : Fin M→Prop) (r : Fin N→Prop) :
    primitiveCharacterMean Q (fun _ χ=>‖triangularCharacterSum
      (sequenceMask p (vaughanFirstSequence V M))
      (sequenceMask r (vaughanSecondSequence U N)) (fun m=>X/m.val+1) χ‖) ≤
      ((k:ℝ)+1)*sieveBilinearConstant Q M N*Real.sqrt M*(Real.sqrt N*Real.log N) := by
  have h:=triangular_primitive_mean_le Q M N k hk
    (sequenceMask p (vaughanFirstSequence V M))
    (sequenceMask r (vaughanSecondSequence U N)) (fun m=>X/m.val+1)
  apply h.trans
  have hC : 0 ≤ ((k:ℝ)+1)*sieveBilinearConstant Q M N :=
    mul_nonneg (by positivity) (sieveBilinearConstant_nonneg _ _ _)
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left
      ((sequenceMask_size_le _ _).trans (vaughanFirstSequence_size_le _ _)) hC
  · exact (sequenceMask_size_le _ _).trans (vaughanSecondSequence_size_le _ _)
  · exact sequenceSize_nonneg _
  · exact mul_nonneg hC (Real.sqrt_nonneg _)

theorem sum_Icc_one_eq_range_of_zero {E : Type*} [AddCommMonoid E]
    (F : ℕ→E) (hF : F 0=0) (N : ℕ) :
    (∑ n∈Finset.Icc 1 N,F n)=∑ n∈Finset.range (N+1),F n := by
  apply Finset.sum_subset
  · intro n hn
    have h:=Finset.mem_Icc.mp hn
    exact Finset.mem_range.mpr (by omega)
  · intro n hn hn'
    have h:=Finset.mem_range.mp hn
    have hh:¬(1 ≤ n ∧ n ≤ N):=by simpa using hn'
    have he:n=0:=by omega
    simpa [he] using hF

theorem sum_range_filter_prefix {E : Type*} [AddCommMonoid E]
    (F : ℕ→E) {N K : ℕ} (hK : K ≤ N) :
    (∑ n∈Finset.range (N+1),if n<K+1 then F n else 0)=
      ∑ n∈Finset.range (K+1),F n := by
  rw [←Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter,Finset.mem_range]
  omega

theorem arithmeticCharacterSum_convolution_triangular {q : ℕ} (X : ℕ)
    (f g : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X (f*g) χ=
      triangularCharacterSum (fun m:Fin (X+1)=>(f m.val:ℂ))
        (fun n:Fin (X+1)=>(g n.val:ℂ)) (fun m=>X/m.val+1) χ := by
  rw [arithmeticCharacterSum_convolution]
  rw [sum_Icc_one_eq_range_of_zero (fun d=>(f d:ℂ)*χ (d:ZMod q)*
    (∑ m∈Finset.Icc 1 (X/d),(g m:ℂ)*χ (m:ZMod q))) (by simp)]
  have he : triangularCharacterSum (fun m:Fin (X+1)=>(f m.val:ℂ))
      (fun n:Fin (X+1)=>(g n.val:ℂ)) (fun m=>X/m.val+1) χ=
      ∑ m∈Finset.range (X+1),∑ n∈Finset.range (X+1),
        if n<X/m+1 then (f m:ℂ)*(g n:ℂ)*χ (m:ZMod q)*χ (n:ZMod q) else 0 := by
    unfold triangularCharacterSum
    trans ∑ m:Fin (X+1),∑ n∈Finset.range (X+1),
      if n<X/m.val+1 then (f m.val:ℂ)*(g n:ℂ)*χ (m.val:ZMod q)*χ (n:ZMod q) else 0
    · apply Finset.sum_congr rfl
      intro m _
      exact Fin.sum_univ_eq_sum_range (fun n:ℕ=>
        if n<X/m.val+1 then (f m.val:ℂ)*(g n:ℂ)*χ (m.val:ZMod q)*χ (n:ZMod q) else 0) _
    · exact Fin.sum_univ_eq_sum_range (fun m:ℕ=>∑ n∈Finset.range (X+1),
        if n<X/m+1 then (f m:ℂ)*(g n:ℂ)*χ (m:ZMod q)*χ (n:ZMod q) else 0) _
  rw [he]
  apply Finset.sum_congr rfl
  intro m _
  rw [sum_Icc_one_eq_range_of_zero (fun n=>(g n:ℂ)*χ (n:ZMod q)) (by simp)]
  rw [←sum_range_filter_prefix (fun n=>(g n:ℂ)*χ (n:ZMod q)) (Nat.div_le_self X m)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> ring

theorem vaughan_typeII_exact {q : ℕ} (X U V : ℕ) (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X
      ((ArithmeticFunction.moebius-arithmeticCutoff V ArithmeticFunction.moebius)*
        vaughanSecondCoefficient U) χ=
      triangularCharacterSum (vaughanFirstSequence V (X+1))
        (vaughanSecondSequence U (X+1)) (fun m=>X/m.val+1) χ := by
  rw [arithmeticCharacterSum_convolution_triangular]
  congr 1
  funext m
  change (((ArithmeticFunction.moebius m.val:ℝ)-
    (if m.val ≤ V then (ArithmeticFunction.moebius m.val:ℝ) else 0):ℝ):ℂ)=_
  by_cases hm:m.val ≤ V
  · simp [vaughanFirstSequence,hm,not_lt_of_ge hm]
  · simp [vaughanFirstSequence,hm,lt_of_not_ge hm]

noncomputable def arithmeticL1 (X : ℕ) (f : ArithmeticFunction ℝ) : ℝ :=
  ∑ n∈Finset.Icc 1 X,|f n|

theorem arithmeticCharacterSum_le_l1 {q : ℕ} (X : ℕ)
    (f : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) :
    ‖arithmeticCharacterSum X f χ‖ ≤ arithmeticL1 X f := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (χ.norm_le_one _)

theorem arithmeticL1_nonneg (X : ℕ) (f : ArithmeticFunction ℝ) :
    0 ≤ arithmeticL1 X f := Finset.sum_nonneg (fun _ _=>abs_nonneg _)

theorem arithmeticL1_cutoff_le (X D : ℕ) (f : ArithmeticFunction ℝ) {A : ℝ}
    (hA : 0 ≤ A) (hf : ∀ n∈Finset.Icc 1 D,|f n| ≤ A) :
    arithmeticL1 X (arithmeticCutoff D f) ≤ (D:ℝ)*A := by
  have he : arithmeticL1 X (arithmeticCutoff D f)=
      ∑ n∈(Finset.Icc 1 X).filter (fun n=>n ≤ D),|f n| := by
    simp only [arithmeticL1,arithmeticCutoff_apply,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs <;> simp
  rw [he]
  have hs : (Finset.Icc 1 X).filter (fun n=>n ≤ D) ⊆ Finset.Icc 1 D := by
    intro n hn
    obtain ⟨hn,hnD⟩:=Finset.mem_filter.mp hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,hnD⟩
  calc
    _ ≤ ∑ _n∈(Finset.Icc 1 X).filter (fun n=>n ≤ D),A :=
      Finset.sum_le_sum (fun n hn=>hf n (hs hn))
    _ = (((Finset.Icc 1 X).filter (fun n=>n ≤ D)).card:ℝ)*A := by simp
    _ ≤ (D:ℝ)*A := by
      apply mul_le_mul_of_nonneg_right _ hA
      exact_mod_cast (by simpa using Finset.card_le_card hs)

theorem arithmeticCharacterSum_log_convolution_bound {q : ℕ} (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (X : ℕ) (f : ArithmeticFunction ℝ) :
    ‖arithmeticCharacterSum X (f*ArithmeticFunction.log) χ‖ ≤
      arithmeticL1 X f*(2*Real.log (X+1:ℕ)*(Real.sqrt q*(harmonic q:ℝ))) := by
  rw [arithmeticCharacterSum_convolution]
  have he (d : ℕ) : (∑ n∈Finset.Icc 1 (X/d),
      (ArithmeticFunction.log n:ℂ)*χ (n:ZMod q))=
      ∑ n∈Finset.range (X/d+1),(Real.log n:ℂ)*χ (n:ZMod q) := by
    exact sum_Icc_one_eq_range_of_zero _ (by simp) _
  simp only [he]
  have h:=primitive_typeI_log_bound hq hχ X X (fun d=>(f d:ℂ))
  simpa only [arithmeticL1,Complex.norm_real,Real.norm_eq_abs] using h

theorem arithmeticCharacterSum_zeta_convolution_bound {q : ℕ} (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (X : ℕ) (f : ArithmeticFunction ℝ) :
    ‖arithmeticCharacterSum X (f*(ArithmeticFunction.zeta:ArithmeticFunction ℝ)) χ‖ ≤
      arithmeticL1 X f*(Real.sqrt q*(harmonic q:ℝ)) := by
  rw [arithmeticCharacterSum_convolution]
  have he (d : ℕ) : (∑ n∈Finset.Icc 1 (X/d),
      ((ArithmeticFunction.zeta:ArithmeticFunction ℝ) n:ℂ)*χ (n:ZMod q))=
      ∑ n∈Finset.range (X/d+1),χ (n:ZMod q) := by
    trans ∑ n∈Finset.Icc 1 (X/d),χ (n:ZMod q)
    · apply Finset.sum_congr rfl
      intro n hn
      have hn0:n≠0:=by have h:=(Finset.mem_Icc.mp hn).1; omega
      simp [ArithmeticFunction.natCoe_apply,ArithmeticFunction.zeta_apply_ne hn0]
    · exact sum_Icc_one_eq_range_of_zero _ (by simpa using χ.map_zero' (by omega)) _
  simp only [he]
  have h:=primitive_typeI_bound hq hχ X X (fun d=>(f d:ℂ))
  simpa only [arithmeticL1,Complex.norm_real,Real.norm_eq_abs] using h

theorem arithmeticCutoff_mul_support (U V n : ℕ) (f g : ArithmeticFunction ℝ)
    (hn : U*V < n) : (arithmeticCutoff U f*arithmeticCutoff V g) n=0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro p hp
  have he:p.1*p.2=n:=(Nat.mem_divisorsAntidiagonal.mp hp).1
  by_cases h1:p.1 ≤ U
  · by_cases h2:p.2 ≤ V
    · have h:=Nat.mul_le_mul h1 h2
      omega
    · simp [arithmeticCutoff_apply,h2]
  · simp [arithmeticCutoff_apply,h1]

theorem vaughanShortCoefficient_abs_le (U V n : ℕ) :
    |(arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ)*
      arithmeticCutoff U ArithmeticFunction.vonMangoldt) n| ≤ Real.log n := by
  rw [ArithmeticFunction.mul_apply]
  calc
    _ ≤ ∑ p∈n.divisorsAntidiagonal,
        |arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ) p.1*
          arithmeticCutoff U ArithmeticFunction.vonMangoldt p.2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p∈n.divisorsAntidiagonal,ArithmeticFunction.vonMangoldt p.2 := by
      apply Finset.sum_le_sum
      intro p _
      rw [abs_mul]
      have hm: |arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ) p.1| ≤ 1 := by
        rw [arithmeticCutoff_apply]
        split_ifs
        · rw [ArithmeticFunction.intCoe_apply]
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=p.1))
        · simp
      have hl: |arithmeticCutoff U ArithmeticFunction.vonMangoldt p.2| ≤
          ArithmeticFunction.vonMangoldt p.2 := by
        rw [arithmeticCutoff_apply]
        split_ifs
        · exact (abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg).le
        · simp
      exact (mul_le_mul hm hl (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = _ := by
      rw [Nat.sum_divisorsAntidiagonal' (fun _ d=>ArithmeticFunction.vonMangoldt d),
        ArithmeticFunction.vonMangoldt_sum]

theorem arithmeticCutoff_eq_of_support (D : ℕ) (f : ArithmeticFunction ℝ)
    (hf : ∀ n,D<n→f n=0) : arithmeticCutoff D f=f := by
  ext n
  by_cases hn:n ≤ D
  · simp [arithmeticCutoff_apply,hn]
  · simp [arithmeticCutoff_apply,hn,hf n (lt_of_not_ge hn)]

theorem vonMangoldt_cutoff_l1 (X U : ℕ) :
    arithmeticL1 X (arithmeticCutoff U ArithmeticFunction.vonMangoldt) ≤ (U:ℝ)*Real.log U := by
  apply arithmeticL1_cutoff_le
  · simpa using log_nat_monotone (Nat.zero_le U)
  · intro n hn
    rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact ArithmeticFunction.vonMangoldt_le_log.trans (log_nat_monotone (Finset.mem_Icc.mp hn).2)

theorem moebius_cutoff_l1 (X V : ℕ) :
    arithmeticL1 X (arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ)) ≤ V := by
  have h:=arithmeticL1_cutoff_le X V (ArithmeticFunction.moebius:ArithmeticFunction ℝ)
    zero_le_one (fun n _=>by
      rw [ArithmeticFunction.intCoe_apply]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=n)))
  simpa only [mul_one] using h

theorem vaughanShortCoefficient_l1 (X U V : ℕ) :
    arithmeticL1 X (arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ)*
      arithmeticCutoff U ArithmeticFunction.vonMangoldt) ≤ (V*U:ℕ)*Real.log (V*U:ℕ) := by
  let f:=arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ)*
    arithmeticCutoff U ArithmeticFunction.vonMangoldt
  have he : arithmeticCutoff (V*U) f=f :=
    arithmeticCutoff_eq_of_support _ _ (fun n hn=>arithmeticCutoff_mul_support V U n _ _ hn)
  change arithmeticL1 X f ≤ _
  rw [←he]
  apply arithmeticL1_cutoff_le
  · simpa using log_nat_monotone (Nat.zero_le (V*U))
  · intro n hn
    exact (vaughanShortCoefficient_abs_le U V n).trans (log_nat_monotone (Finset.mem_Icc.mp hn).2)

theorem primitive_vaughan_bound {q : ℕ} (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (X U V : ℕ) :
    ‖arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ‖ ≤
      (U:ℝ)*Real.log U+
      (V:ℝ)*(2*Real.log (X+1:ℕ)*(Real.sqrt q*(harmonic q:ℝ)))+
      ((V*U:ℕ)*Real.log (V*U:ℕ))*(Real.sqrt q*(harmonic q:ℝ))+
      ‖triangularCharacterSum (vaughanFirstSequence V (X+1))
        (vaughanSecondSequence U (X+1)) (fun m=>X/m.val+1) χ‖ := by
  have hH : 0 ≤ (harmonic q:ℝ) := by exact_mod_cast (harmonic_pos (by omega : q≠0)).le
  have hK : 0 ≤ Real.sqrt q*(harmonic q:ℝ) := mul_nonneg (Real.sqrt_nonneg _) hH
  have hL : 0 ≤ (2:ℝ)*Real.log (X+1:ℕ)*(Real.sqrt q*(harmonic q:ℝ)) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ X+1 by omega)))) hK
  have h0 := (arithmeticCharacterSum_le_l1 X (arithmeticCutoff U ArithmeticFunction.vonMangoldt) χ).trans
    (vonMangoldt_cutoff_l1 X U)
  have h1 := (arithmeticCharacterSum_log_convolution_bound hq hχ X
    (arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ))).trans
      (mul_le_mul_of_nonneg_right (moebius_cutoff_l1 X V) hL)
  have h2 := (arithmeticCharacterSum_zeta_convolution_bound hq hχ X
    (arithmeticCutoff V (ArithmeticFunction.moebius:ArithmeticFunction ℝ)*
      arithmeticCutoff U ArithmeticFunction.vonMangoldt)).trans
      (mul_le_mul_of_nonneg_right (vaughanShortCoefficient_l1 X U V) hK)
  rw [vaughan_character_identity,vaughan_typeII_exact]
  apply le_trans (norm_add_le _ _)
  apply add_le_add _ le_rfl
  apply le_trans (norm_sub_le _ _)
  apply add_le_add _ h2
  exact (norm_add_le _ _).trans (add_le_add h0 h1)

noncomputable def hyperbolaBlock {q : ℕ} (X D E : ℕ)
    (a b : ℕ→ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ m∈Finset.Ico D E,a m*χ (m:ZMod q)*
    (∑ n∈Finset.range (X/m+1),b n*χ (n:ZMod q))

theorem hyperbolaBlock_eq_triangle {q : ℕ} (X D E : ℕ) (hD : 0 < D)
    (a b : ℕ→ℂ) (χ : DirichletCharacter ℂ q) :
    hyperbolaBlock X D E a b χ=
      triangularCharacterSum (sequenceMask (fun m:Fin E=>D ≤ m.val) (fun m=>a m.val))
        (fun n:Fin (X/D+1)=>b n.val) (fun m=>X/m.val+1) χ := by
  classical
  have hf : (Finset.range E).filter (fun m=>D ≤ m)=Finset.Ico D E := by
    ext m
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
    omega
  have he : triangularCharacterSum
      (sequenceMask (fun m:Fin E=>D ≤ m.val) (fun m=>a m.val))
      (fun n:Fin (X/D+1)=>b n.val) (fun m=>X/m.val+1) χ=
      ∑ m∈Finset.range E,∑ n∈Finset.range (X/D+1),
        if n < X/m+1 then (if D ≤ m then a m else 0)*b n*χ (m:ZMod q)*χ (n:ZMod q) else 0 := by
    unfold triangularCharacterSum sequenceMask
    trans ∑ m:Fin E,∑ n∈Finset.range (X/D+1),
      if n < X/m.val+1 then (if D ≤ m.val then a m.val else 0)*b n*χ (m.val:ZMod q)*χ (n:ZMod q) else 0
    · apply Finset.sum_congr rfl
      intro m _
      by_cases hm:D ≤ m.val <;>
        simpa only [hm,ite_true,ite_false] using
          (Fin.sum_univ_eq_sum_range (fun n:ℕ=>
            if n < X/m.val+1 then (if D ≤ m.val then a m.val else 0)*b n*χ (m.val:ZMod q)*χ (n:ZMod q) else 0) (X/D+1))
    · exact Fin.sum_univ_eq_sum_range (fun m:ℕ=>∑ n∈Finset.range (X/D+1),
        if n < X/m+1 then (if D ≤ m then a m else 0)*b n*χ (m:ZMod q)*χ (n:ZMod q) else 0) _
  rw [he]
  unfold hyperbolaBlock
  rw [←hf,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm:D ≤ m
  · simp only [hm,ite_true]
    rw [←sum_range_filter_prefix (fun n=>b n*χ (n:ZMod q)) (Nat.div_le_div_left hm hD)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs <;> ring
  · simp [hm]

theorem sum_Ico_one_pow_two {A : Type*} [AddCommMonoid A] (F : ℕ→A) (k : ℕ) :
    (∑ m∈Finset.Ico 1 (2^k),F m)=
      ∑ j∈Finset.range k,∑ m∈Finset.Ico (2^j) (2^(j+1)),F m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ,←ih,Finset.sum_Ico_consecutive]
    · exact one_le_pow₀ (by omega)
    · exact pow_le_pow_right₀ (by omega) (Nat.le_succ k)

theorem vaughan_hyperbolaBlock_mean (Q X U V D E k : ℕ) (hD : 0 < D)
    (hk : X/D+1 ≤ 2^k) :
    primitiveCharacterMean Q (fun _ χ=>‖hyperbolaBlock X D E
      (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
      (fun n=>(vaughanSecondCoefficient U n:ℂ)) χ‖) ≤
      ((k:ℝ)+1)*sieveBilinearConstant Q E (X/D+1)*Real.sqrt E*
        (Real.sqrt ((X/D+1:ℕ):ℝ)*Real.log ((X/D+1:ℕ):ℝ)) := by
  have h:=vaughan_typeII_block_mean Q X U V E (X/D+1) k hk
    (fun m=>D ≤ m.val) (fun _=>True)
  have hr : sequenceMask (fun _ : Fin (X/D+1)=>True)
      (vaughanSecondSequence U (X/D+1))=vaughanSecondSequence U (X/D+1) := by
    funext n
    simp [sequenceMask]
  rw [hr] at h
  have he : (fun (_q : Fin Q) (χ : DirichletCharacter ℂ (_q.val+1))=>‖hyperbolaBlock X D E
      (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
      (fun n=>(vaughanSecondCoefficient U n:ℂ)) χ‖)=
      (fun (_q : Fin Q) (χ : DirichletCharacter ℂ (_q.val+1))=>‖triangularCharacterSum
        (sequenceMask (fun m:Fin E=>D ≤ m.val) (vaughanFirstSequence V E))
        (vaughanSecondSequence U (X/D+1)) (fun m=>X/m.val+1) χ‖) := by
    funext q χ
    rw [hyperbolaBlock_eq_triangle X D E hD]
    rfl
  rw [he]
  exact h

theorem hyperbolaBlock_extend {q : ℕ} (X E : ℕ) (hE : X+1 ≤ E)
    (a b : ℕ→ℂ) (hb : b 0=0) (χ : DirichletCharacter ℂ q) :
    hyperbolaBlock X 1 (X+1) a b χ=hyperbolaBlock X 1 E a b χ := by
  unfold hyperbolaBlock
  apply Finset.sum_subset
  · intro m hm
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hm).1,
      ((Finset.mem_Ico.mp hm).2).trans_le hE⟩
  · intro m hm hm'
    have hx : X < m := by
      have h:=Finset.mem_Ico.mp hm
      have hh : ¬(1 ≤ m ∧ m < X+1) := by simpa only [Finset.mem_Ico] using hm'
      omega
    simp [Nat.div_eq_of_lt hx,hb]

theorem arithmeticCharacterSum_convolution_dyadic {q : ℕ} (X k : ℕ)
    (hk : X+1 ≤ 2^k) (f g : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X (f*g) χ=
      ∑ j∈Finset.range k,hyperbolaBlock X (2^j) (2^(j+1))
        (fun m=>(f m:ℂ)) (fun n=>(g n:ℂ)) χ := by
  rw [arithmeticCharacterSum_convolution]
  have he : (∑ m∈Finset.Icc 1 X,(f m:ℂ)*χ (m:ZMod q)*
      ∑ n∈Finset.Icc 1 (X/m),(g n:ℂ)*χ (n:ZMod q))=
      hyperbolaBlock X 1 (X+1) (fun m=>(f m:ℂ)) (fun n=>(g n:ℂ)) χ := by
    unfold hyperbolaBlock
    rw [show Finset.Ico 1 (X+1)=Finset.Icc 1 X by ext m; simp]
    apply Finset.sum_congr rfl
    intro m _
    rw [sum_Icc_one_eq_range_of_zero (fun n=>(g n:ℂ)*χ (n:ZMod q)) (by simp)]
  rw [he,hyperbolaBlock_extend X (2^k) hk _ _ (by simp)]
  exact sum_Ico_one_pow_two _ k

theorem vaughan_typeII_dyadic {q : ℕ} (X U V k : ℕ) (hk : X+1 ≤ 2^k)
    (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X
      ((ArithmeticFunction.moebius-arithmeticCutoff V ArithmeticFunction.moebius)*
        vaughanSecondCoefficient U) χ=
      ∑ j∈Finset.range k,hyperbolaBlock X (2^j) (2^(j+1))
        (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
        (fun n=>(vaughanSecondCoefficient U n:ℂ)) χ := by
  rw [arithmeticCharacterSum_convolution_dyadic X k hk]
  have hf : (fun m=>(((ArithmeticFunction.moebius-
        arithmeticCutoff V ArithmeticFunction.moebius):ArithmeticFunction ℝ) m:ℂ))=
      (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0) := by
    funext m
    change (((ArithmeticFunction.moebius m:ℝ)-
      (if m ≤ V then (ArithmeticFunction.moebius m:ℝ) else 0):ℝ):ℂ)=_
    by_cases hm:m ≤ V
    · simp [hm,not_lt_of_ge hm]
    · simp [hm,lt_of_not_ge hm]
  rw [hf]

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_VaughanBounds

section File_OpenAIPrimeGaps_DyadicMeans

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

theorem primitiveCharacterMean_sum {ι : Type*} (Q : ℕ) (s : Finset ι)
    (f : ι→(q:Fin Q)→DirichletCharacter ℂ (q.val+1)→ℝ) :
    primitiveCharacterMean Q (fun q χ=>∑ i∈s,f i q χ)=
      ∑ i∈s,primitiveCharacterMean Q (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [primitiveCharacterMean]
  | cons a s ha ih =>
    simp only [Finset.sum_cons,primitiveCharacterMean_add,ih]

theorem vaughan_typeII_dyadic_mean (Q X U V k : ℕ) (hk : X+1 ≤ 2^k) :
    primitiveCharacterMean Q (fun _ χ=>‖arithmeticCharacterSum X
      ((ArithmeticFunction.moebius-arithmeticCutoff V ArithmeticFunction.moebius)*
        vaughanSecondCoefficient U) χ‖) ≤
      ∑ j∈Finset.range k,((k:ℝ)+1)*sieveBilinearConstant Q (2^(j+1)) (X/2^j+1)*
        Real.sqrt ((2^(j+1):ℕ):ℝ)*
          (Real.sqrt ((X/2^j+1:ℕ):ℝ)*Real.log ((X/2^j+1:ℕ):ℝ)) := by
  have h:=primitiveCharacterMean_mono (Q:=Q)
    (f:=fun _ χ=>‖arithmeticCharacterSum X
      ((ArithmeticFunction.moebius-arithmeticCutoff V ArithmeticFunction.moebius)*
        vaughanSecondCoefficient U) χ‖)
    (g:=fun _ χ=>∑ j∈Finset.range k,‖hyperbolaBlock X (2^j) (2^(j+1))
      (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
      (fun n=>(vaughanSecondCoefficient U n:ℂ)) χ‖) (fun _ χ=>by
        rw [vaughan_typeII_dyadic X U V k hk]
        exact norm_sum_le _ _)
  rw [primitiveCharacterMean_sum] at h
  apply h.trans
  apply Finset.sum_le_sum
  intro j _
  exact vaughan_hyperbolaBlock_mean Q X U V (2^j) (2^(j+1)) k
    (pow_pos (by omega) _) ((Nat.add_le_add_right (Nat.div_le_self _ _) 1).trans hk)

theorem vaughan_hyperbolaBlock_zero_left {q : ℕ} (X U V D E : ℕ)
    (hE : E ≤ V+1) (χ : DirichletCharacter ℂ q) :
    hyperbolaBlock X D E
      (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
      (fun n=>(vaughanSecondCoefficient U n:ℂ)) χ=0 := by
  apply Finset.sum_eq_zero
  intro m hm
  have h:=Finset.mem_Ico.mp hm
  have hn:¬V < m:=by omega
  simp [hn]

theorem vaughan_hyperbolaBlock_zero_right {q : ℕ} (X U V D E : ℕ)
    (hD : 0 < D) (hU : X/D ≤ U) (χ : DirichletCharacter ℂ q) :
    hyperbolaBlock X D E
      (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
      (fun n=>(vaughanSecondCoefficient U n:ℂ)) χ=0 := by
  apply Finset.sum_eq_zero
  intro m hm
  have hmD: D ≤ m:=(Finset.mem_Ico.mp hm).1
  have hnU:X/m ≤ U:=(Nat.div_le_div_left hmD hD).trans hU
  have hz:(∑ n∈Finset.range (X/m+1),(vaughanSecondCoefficient U n:ℂ)*χ (n:ZMod q))=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnle:n ≤ U:=by have h:=Finset.mem_range.mp hn; omega
    simp [vaughanSecondCoefficient_zero_of_le hnle]
  rw [hz,mul_zero]

theorem vaughan_typeII_active_dyadic {q : ℕ} (X U V k : ℕ) (hk : X+1 ≤ 2^k)
    (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X
      ((ArithmeticFunction.moebius-arithmeticCutoff V ArithmeticFunction.moebius)*
        vaughanSecondCoefficient U) χ=
      ∑ j∈(Finset.range k).filter (fun j=>V+1 < 2^(j+1) ∧ U < X/2^j),
        hyperbolaBlock X (2^j) (2^(j+1))
          (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
          (fun n=>(vaughanSecondCoefficient U n:ℂ)) χ := by
  rw [vaughan_typeII_dyadic X U V k hk]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j hj hj'
  have hneg:¬(V+1 < 2^(j+1) ∧ U < X/2^j) := by
    simpa only [Finset.mem_filter,hj,true_and] using hj'
  by_cases hl:V+1 < 2^(j+1)
  · exact vaughan_hyperbolaBlock_zero_right X U V (2^j) (2^(j+1))
      (pow_pos (by omega) _) (by omega) χ
  · exact vaughan_hyperbolaBlock_zero_left X U V (2^j) (2^(j+1)) (by omega) χ

theorem vaughan_typeII_active_mean (Q X U V k : ℕ) (hk : X+1 ≤ 2^k) :
    primitiveCharacterMean Q (fun _ χ=>‖arithmeticCharacterSum X
      ((ArithmeticFunction.moebius-arithmeticCutoff V ArithmeticFunction.moebius)*
        vaughanSecondCoefficient U) χ‖) ≤
      ∑ j∈(Finset.range k).filter (fun j=>V+1 < 2^(j+1) ∧ U < X/2^j),
        ((k:ℝ)+1)*sieveBilinearConstant Q (2^(j+1)) (X/2^j+1)*
          Real.sqrt ((2^(j+1):ℕ):ℝ)*
            (Real.sqrt ((X/2^j+1:ℕ):ℝ)*Real.log ((X/2^j+1:ℕ):ℝ)) := by
  have h:=primitiveCharacterMean_mono (Q:=Q)
    (f:=fun _ χ=>‖arithmeticCharacterSum X
      ((ArithmeticFunction.moebius-arithmeticCutoff V ArithmeticFunction.moebius)*
        vaughanSecondCoefficient U) χ‖)
    (g:=fun _ χ=>∑ j∈(Finset.range k).filter (fun j=>V+1 < 2^(j+1) ∧ U < X/2^j),
      ‖hyperbolaBlock X (2^j) (2^(j+1))
        (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
        (fun n=>(vaughanSecondCoefficient U n:ℂ)) χ‖) (fun _ χ=>by
          rw [vaughan_typeII_active_dyadic X U V k hk]
          exact norm_sum_le _ _)
  rw [primitiveCharacterMean_sum] at h
  apply h.trans
  apply Finset.sum_le_sum
  intro j _
  exact vaughan_hyperbolaBlock_mean Q X U V (2^j) (2^(j+1)) k
    (pow_pos (by omega) _) ((Nat.add_le_add_right (Nat.div_le_self _ _) 1).trans hk)

theorem sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a+b) ≤ Real.sqrt a+Real.sqrt b := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt (add_nonneg ha hb)]
  nlinarith [Real.sq_sqrt ha,Real.sq_sqrt hb,Real.sqrt_nonneg a,Real.sqrt_nonneg b]

theorem sqrt_bilinear_expansion {m n z : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n) (hz : 0 ≤ z) :
    (Real.sqrt (m+z)*Real.sqrt (n+z))*Real.sqrt m*Real.sqrt n ≤
      m*n+Real.sqrt z*(m*Real.sqrt n+n*Real.sqrt m)+z*Real.sqrt m*Real.sqrt n := by
  have h:=mul_le_mul (sqrt_add_le_sqrt_add_sqrt hm hz) (sqrt_add_le_sqrt_add_sqrt hn hz)
    (Real.sqrt_nonneg _) (by positivity : 0 ≤ Real.sqrt m+Real.sqrt z)
  calc
    _ ≤ ((Real.sqrt m+Real.sqrt z)*(Real.sqrt n+Real.sqrt z))*Real.sqrt m*Real.sqrt n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    _ = (Real.sqrt m)^2*(Real.sqrt n)^2+
        Real.sqrt z*((Real.sqrt m)^2*Real.sqrt n+(Real.sqrt n)^2*Real.sqrt m)+
        (Real.sqrt z)^2*Real.sqrt m*Real.sqrt n := by ring
    _ = _ := by rw [Real.sq_sqrt hm,Real.sq_sqrt hn,Real.sq_sqrt hz]

theorem sqrt_product_le_twice {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : 0 ≤ x) (hab : a*b ≤ 4*x) :
    Real.sqrt a*Real.sqrt b ≤ 2*Real.sqrt x := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow,mul_pow,Real.sq_sqrt ha,Real.sq_sqrt hb,Real.sq_sqrt hx]
  norm_num
  exact hab

theorem sqrt_bilinear_hyperbolic_bound {m n x t z : ℝ}
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hx : 0 ≤ x) (ht : 0 < t) (hz : 0 ≤ z)
    (hmn : m*n ≤ 4*x) (hmt : m*t ≤ 4*x) (hnt : n*t ≤ 4*x) :
    (Real.sqrt (m+z)*Real.sqrt (n+z))*Real.sqrt m*Real.sqrt n ≤
      4*x+Real.sqrt z*(8*x/Real.sqrt t)+z*(2*Real.sqrt x) := by
  have hmn' := sqrt_product_le_twice hm hn hx hmn
  have hmt' := sqrt_product_le_twice hm ht.le hx hmt
  have hnt' := sqrt_product_le_twice hn ht.le hx hnt
  have hcross : (m*Real.sqrt n+n*Real.sqrt m)*Real.sqrt t ≤ 8*x := by
    calc
      _ = (Real.sqrt m*Real.sqrt n)*
          (Real.sqrt m*Real.sqrt t+Real.sqrt n*Real.sqrt t) := by
        calc
          _ = ((Real.sqrt m)^2*Real.sqrt n+(Real.sqrt n)^2*Real.sqrt m)*Real.sqrt t := by
            rw [Real.sq_sqrt hm,Real.sq_sqrt hn]
          _ = _ := by ring
      _ ≤ (2*Real.sqrt x)*(4*Real.sqrt x) :=
        mul_le_mul hmn' (by linarith) (by positivity) (by positivity)
      _ = _ := by nlinarith [Real.sq_sqrt hx]
  have hc : m*Real.sqrt n+n*Real.sqrt m ≤ 8*x/Real.sqrt t :=
    (le_div_iff₀ (Real.sqrt_pos.mpr ht)).mpr hcross
  apply (sqrt_bilinear_expansion hm hn hz).trans
  simpa only [mul_assoc] using
    (add_le_add (add_le_add hmn (mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg _)))
      (mul_le_mul_of_nonneg_left hmn' hz))

theorem vaughan_active_dimensions (X T j : ℕ)
    (hleft : T+1 < 2^(j+1)) (hright : T < X/2^j) :
    (2^(j+1))*(X/2^j+1) ≤ 4*X ∧
    (2^(j+1))*(T+1) ≤ 4*X ∧ (X/2^j+1)*(T+1) ≤ 4*X := by
  have hD : 0 < 2^j := pow_pos (by omega) _
  have hprod : (T+1)*2^j ≤ X := (Nat.le_div_iff_mul_le hD).mp (by omega)
  have hX : 2^j ≤ X := by nlinarith
  have hdiv := Nat.div_mul_le_self X (2^j)
  have hpow : 2^(j+1)=2*2^j := by rw [pow_succ]; omega
  have harea : (2^(j+1))*(X/2^j+1) ≤ 4*X := by rw [hpow]; nlinarith
  refine ⟨harea,?_,?_⟩
  · rw [hpow]
    nlinarith
  · exact (Nat.mul_le_mul_left (X/2^j+1) hleft.le).trans (by simpa only [Nat.mul_comm] using harea)

noncomputable def vaughanBilinearBound (Q X T : ℕ) : ℝ :=
  let z:ℝ:=(Q:ℝ)^2*(harmonic (Q^2):ℝ)
  4*(X:ℝ)+Real.sqrt z*(8*(X:ℝ)/Real.sqrt (T+1:ℕ))+z*(2*Real.sqrt X)

theorem harmonic_real_nonneg (n : ℕ) : 0 ≤ (harmonic n:ℝ) := by
  by_cases hn:n=0
  · simp [hn]
  · exact_mod_cast (harmonic_pos hn).le

theorem vaughanBilinearBound_nonneg (Q X T : ℕ) : 0 ≤ vaughanBilinearBound Q X T := by
  have hh:=harmonic_real_nonneg (Q^2)
  unfold vaughanBilinearBound
  positivity

theorem vaughan_active_bilinear_bound (Q X T j : ℕ)
    (hleft : T+1 < 2^(j+1)) (hright : T < X/2^j) :
    sieveBilinearConstant Q (2^(j+1)) (X/2^j+1)*
      Real.sqrt ((2^(j+1):ℕ):ℝ)*Real.sqrt ((X/2^j+1:ℕ):ℝ) ≤
        vaughanBilinearBound Q X T := by
  obtain ⟨hmn,hmt,hnt⟩:=vaughan_active_dimensions X T j hleft hright
  apply sqrt_bilinear_hyperbolic_bound (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (by positivity) (mul_nonneg (sq_nonneg _) (harmonic_real_nonneg _))
  · exact_mod_cast hmn
  · exact_mod_cast hmt
  · exact_mod_cast hnt

theorem vaughan_typeII_equal_cutoff_mean (Q X T k : ℕ) (hk : X+1 ≤ 2^k) :
    primitiveCharacterMean Q (fun _ χ=>‖arithmeticCharacterSum X
      ((ArithmeticFunction.moebius-arithmeticCutoff T ArithmeticFunction.moebius)*
        vaughanSecondCoefficient T) χ‖) ≤
      (k:ℝ)*((k:ℝ)+1)*vaughanBilinearBound Q X T*Real.log (X+1:ℕ) := by
  apply (vaughan_typeII_active_mean Q X T T k hk).trans
  let K:=((k:ℝ)+1)*vaughanBilinearBound Q X T*Real.log (X+1:ℕ)
  have hK : 0 ≤ K := mul_nonneg
    (mul_nonneg (by positivity) (vaughanBilinearBound_nonneg _ _ _))
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ X+1 by omega)))
  apply le_trans (b:=∑ _j∈(Finset.range k).filter (fun j=>T+1 < 2^(j+1) ∧ T < X/2^j),K)
  · apply Finset.sum_le_sum
    intro j hj
    obtain ⟨hl,hr⟩ := (Finset.mem_filter.mp hj).2
    have hb:=vaughan_active_bilinear_bound Q X T j hl hr
    have hlog : Real.log ((X/2^j+1:ℕ):ℝ) ≤ Real.log (X+1:ℕ) :=
      log_nat_monotone (Nat.add_le_add_right (Nat.div_le_self _ _) 1)
    have hlog0 : 0 ≤ Real.log ((X/2^j+1:ℕ):ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ X/2^j+1 by omega))
    calc
      _ = ((k:ℝ)+1)*(sieveBilinearConstant Q (2^(j+1)) (X/2^j+1)*
          Real.sqrt ((2^(j+1):ℕ):ℝ)*Real.sqrt ((X/2^j+1:ℕ):ℝ))*
            Real.log ((X/2^j+1:ℕ):ℝ) := by ring
      _ ≤ K := mul_le_mul (mul_le_mul_of_nonneg_left hb (by positivity)) hlog hlog0
        (mul_nonneg (by positivity) (vaughanBilinearBound_nonneg _ _ _))
  · rw [Finset.sum_const,nsmul_eq_mul]
    have hc : (((Finset.range k).filter (fun j=>T+1 < 2^(j+1) ∧ T < X/2^j)).card:ℝ) ≤ k := by
      exact_mod_cast (Finset.card_filter_le (Finset.range k) _).trans_eq (Finset.card_range k)
    exact (mul_le_mul_of_nonneg_right hc hK).trans_eq (by dsimp [K]; ring)

theorem primitiveCharacterMean_mono_primitive {Q : ℕ}
    {f g : (q:Fin Q)→DirichletCharacter ℂ (q.val+1)→ℝ}
    (h : ∀ q χ,χ.IsPrimitive→f q χ ≤ g q χ) :
    primitiveCharacterMean Q f ≤ primitiveCharacterMean Q g := by
  apply Finset.sum_le_sum
  intro q _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro χ hχ
  exact h q χ (Finset.mem_filter.mp hχ).2

theorem primitiveCharacterMean_constant_le (Q : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    primitiveCharacterMean Q (fun _ _=>A) ≤ (Q:ℝ)^2*A := by
  classical
  calc
    _ ≤ ∑ _q:Fin Q,(Q:ℝ)*A := by
      apply Finset.sum_le_sum
      intro q _
      let d:=q.val+1
      have hd:0 < d:=by dsimp [d]; omega
      let : NeZero d:=⟨by omega⟩
      have hphi:0 < (d.totient:ℝ):=by exact_mod_cast Nat.totient_pos.mpr hd
      have hcard:Fintype.card (DirichletCharacter ℂ d)=d.totient := by
        simpa only [Nat.card_eq_fintype_card] using
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d
      have hnum:(((Finset.univ : Finset (DirichletCharacter ℂ d)).filter
          DirichletCharacter.IsPrimitive).card:ℝ) ≤ d.totient := by
        exact_mod_cast (Finset.card_filter_le (Finset.univ : Finset (DirichletCharacter ℂ d)) _).trans_eq
          (by rw [Finset.card_univ,hcard])
      change (d:ℝ)/d.totient*(∑ _χ∈(Finset.univ : Finset (DirichletCharacter ℂ d)).filter
        DirichletCharacter.IsPrimitive,A) ≤ _
      rw [Finset.sum_const,nsmul_eq_mul]
      calc
        _ ≤ (d:ℝ)/d.totient*((d.totient:ℝ)*A) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnum hA) (by positivity)
        _ = (d:ℝ)*A := by field_simp
        _ ≤ (Q:ℝ)*A := mul_le_mul_of_nonneg_right (by exact_mod_cast (show d ≤ Q by dsimp [d]; omega)) hA
    _ = _ := by simp; ring

noncomputable def vaughanShortBound (Q X T : ℕ) : ℝ :=
  let K:=Real.sqrt Q*(1+Real.log Q)
  (T:ℝ)*Real.log T+(T:ℝ)*(2*Real.log (X+1:ℕ)*K)+
    ((T*T:ℕ)*Real.log (T*T:ℕ))*K

theorem log_nat_nonneg (n : ℕ) : 0 ≤ Real.log (n:ℝ) := by
  simpa using log_nat_monotone (Nat.zero_le n)

theorem vaughanShortBound_nonneg (Q X T : ℕ) : 0 ≤ vaughanShortBound Q X T := by
  have hQ:=log_nat_nonneg Q
  have hT:=log_nat_nonneg T
  have hX:=log_nat_nonneg (X+1)
  have hTT:=log_nat_nonneg (T*T)
  unfold vaughanShortBound
  positivity

theorem polya_constant_le {q Q : ℕ} (hqQ : q ≤ Q) :
    Real.sqrt q*(harmonic q:ℝ) ≤ Real.sqrt Q*(1+Real.log Q) := by
  apply mul_le_mul (Real.sqrt_le_sqrt (by exact_mod_cast hqQ))
    ((harmonic_le_one_add_log q).trans (add_le_add le_rfl (log_nat_monotone hqQ)))
    (harmonic_real_nonneg _) (Real.sqrt_nonneg _)

theorem primitive_vaughan_bound_uniform {q Q : ℕ} (hq : 1 < q) (hqQ : q ≤ Q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (X T : ℕ) :
    ‖arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ‖ ≤
      vaughanShortBound Q X T+
      ‖arithmeticCharacterSum X
        ((ArithmeticFunction.moebius-arithmeticCutoff T ArithmeticFunction.moebius)*
          vaughanSecondCoefficient T) χ‖ := by
  rw [vaughan_typeII_exact]
  apply (primitive_vaughan_bound hq hχ X T T).trans
  apply add_le_add_left
  unfold vaughanShortBound
  apply add_le_add
  · apply add_le_add_right
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (polya_constant_le hqQ)
      (mul_nonneg (by norm_num) (log_nat_nonneg _))) (Nat.cast_nonneg _)
  · exact mul_le_mul_of_nonneg_left (polya_constant_le hqQ)
      (mul_nonneg (Nat.cast_nonneg _) (log_nat_nonneg _))

theorem finite_vaughan_primitive_mean (Q X T k : ℕ) (hk : X+1 ≤ 2^k) :
    primitiveCharacterMean Q (fun q χ=>if 1 < q.val+1 then
      ‖arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ‖ else 0) ≤
      (Q:ℝ)^2*vaughanShortBound Q X T+
        (k:ℝ)*((k:ℝ)+1)*vaughanBilinearBound Q X T*Real.log (X+1:ℕ) := by
  have h:=primitiveCharacterMean_mono_primitive (Q:=Q)
    (f:=fun q χ=>if 1 < q.val+1 then ‖arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ‖ else 0)
    (g:=fun _ χ=>vaughanShortBound Q X T+
      ‖arithmeticCharacterSum X
        ((ArithmeticFunction.moebius-arithmeticCutoff T ArithmeticFunction.moebius)*
          vaughanSecondCoefficient T) χ‖) (fun q χ hχ=>by
      by_cases hq:1 < q.val+1
      · rw [ite_eq_left hq]
        exact primitive_vaughan_bound_uniform hq (by omega) hχ X T
      · rw [ite_eq_right hq]
        exact add_nonneg (vaughanShortBound_nonneg _ _ _) (norm_nonneg _))
  rw [primitiveCharacterMean_add] at h
  exact h.trans (add_le_add (primitiveCharacterMean_constant_le _ (vaughanShortBound_nonneg _ _ _))
    (vaughan_typeII_equal_cutoff_mean Q X T k hk))

theorem primitive_ne_one {q : ℕ} (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : χ ≠ 1 := by
  let : NeZero q:=⟨by omega⟩
  intro he
  have hc:=hχ
  rw [DirichletCharacter.isPrimitive_def,he,DirichletCharacter.conductor_one] at hc
  omega

theorem primeCharacterPrefix_nat {q : ℕ} (X : ℕ) (χ : DirichletCharacter ℂ q) :
    primeCharacterPrefix (X:ℝ) χ=arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ := by
  have he : Finset.Ioc 0 X=Finset.Icc 1 X := by ext n; simp; omega
  simp only [primeCharacterPrefix,arithmeticCharacterSum,Nat.floor_natCast,he,mul_comm]

theorem primitiveErrorMass_eq_vonMangoldt_sum (X : ℕ) {q : ℕ} (hq : 1 < q) :
    primitiveErrorMass (X:ℝ) q=
      ∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ q)).filter DirichletCharacter.IsPrimitive,
        ‖arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ‖ := by
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [primeCharacterError,ite_eq_right (primitive_ne_one hq (Finset.mem_filter.mp hχ).2),
    sub_zero,primeCharacterPrefix_nat]

theorem sum_Icc_one_eq_sum_fin {A : Type*} [AddCommMonoid A] (F : ℕ→A) (Q : ℕ) :
    (∑ d∈Finset.Icc 1 Q,F d)=∑ q:Fin Q,F (q.val+1) := by
  classical
  apply Finset.sum_bij (fun d hd=>(⟨d-1,by have h:=Finset.mem_Icc.mp hd; omega⟩:Fin Q))
  · intro d hd
    exact Finset.mem_univ _
  · intro a ha b hb he
    have hh:=congrArg Fin.val he
    have h1:=Finset.mem_Icc.mp ha
    have h2:=Finset.mem_Icc.mp hb
    dsimp at hh
    omega
  · intro q _
    refine ⟨q.val+1,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩
    apply Fin.ext
    simp
  · intro d hd
    have h:=Finset.mem_Icc.mp hd
    simp only [show d-1+1=d by omega]

theorem conductor_interval_error_le_vaughan (Q X T k R : ℕ) (hR : 1 ≤ R)
    (hk : X+1 ≤ 2^k) :
    (R:ℝ)*(∑ d∈Finset.Ioc R Q,primitiveErrorMass (X:ℝ) d/(d.totient:ℝ)) ≤
      (Q:ℝ)^2*vaughanShortBound Q X T+
        (k:ℝ)*((k:ℝ)+1)*vaughanBilinearBound Q X T*Real.log (X+1:ℕ) := by
  have hf : (Finset.Icc 1 Q).filter (fun d=>R < d)=Finset.Ioc R Q := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc]
    omega
  have he : (∑ d∈Finset.Ioc R Q,primitiveErrorMass (X:ℝ) d/(d.totient:ℝ))=
      ∑ q:Fin Q,if R < q.val+1 then primitiveErrorMass (X:ℝ) (q.val+1)/((q.val+1).totient:ℝ) else 0 := by
    rw [←hf,Finset.sum_filter,sum_Icc_one_eq_sum_fin]
  rw [he,Finset.mul_sum]
  apply le_trans (b:=primitiveCharacterMean Q (fun q χ=>if 1 < q.val+1 then
    ‖arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ‖ else 0))
  · apply Finset.sum_le_sum
    intro q _
    by_cases hq:R < q.val+1
    · have hq1:1 < q.val+1:=by omega
      simp only [ite_eq_left hq,ite_eq_left hq1]
      rw [←primitiveErrorMass_eq_vonMangoldt_sum X hq1]
      have hrq:(R:ℝ) ≤ q.val+1:=by exact_mod_cast hq.le
      calc
        _ ≤ ((q.val+1:ℕ):ℝ)*(primitiveErrorMass (X:ℝ) (q.val+1)/((q.val+1).totient:ℝ)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hq.le)
            (div_nonneg (primitiveErrorMass_nonneg _ _) (Nat.cast_nonneg _))
        _ = _ := by ring
    · simp only [ite_eq_right hq,mul_zero]
      apply mul_nonneg (by positivity)
      apply Finset.sum_nonneg
      intro χ _
      split_ifs <;> positivity
  · exact finite_vaughan_primitive_mean Q X T k hk

theorem vaughanShortBound_mono {Q P : ℕ} (hQP : Q ≤ P) (X T : ℕ) :
    vaughanShortBound Q X T ≤ vaughanShortBound P X T := by
  have hK : Real.sqrt Q*(1+Real.log Q) ≤ Real.sqrt P*(1+Real.log P) :=
    mul_le_mul (Real.sqrt_le_sqrt (by exact_mod_cast hQP))
      (add_le_add le_rfl (log_nat_monotone hQP))
      (by have h:=log_nat_nonneg Q; positivity) (Real.sqrt_nonneg _)
  unfold vaughanShortBound
  exact add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK
      (mul_nonneg (by norm_num) (log_nat_nonneg _))) (Nat.cast_nonneg _)))
    (mul_le_mul_of_nonneg_left hK (mul_nonneg (Nat.cast_nonneg _) (log_nat_nonneg _)))

noncomputable def conductorHarmonicBound (Q : ℕ) : ℝ := 1+Real.log (Q^2:ℕ)

theorem conductorHarmonicBound_pos (Q : ℕ) : 0 < conductorHarmonicBound Q := by
  unfold conductorHarmonicBound
  have h:=log_nat_nonneg (Q^2)
  linarith

theorem conductor_harmonic_le {q Q : ℕ} (hqQ : q ≤ Q) :
    (harmonic (q^2):ℝ) ≤ conductorHarmonicBound Q := by
  exact (harmonic_le_one_add_log _).trans
    (add_le_add le_rfl (log_nat_monotone (Nat.pow_le_pow_left hqQ 2)))

noncomputable def highConductorBlockBound (Q X T R k : ℕ) : ℝ :=
  2*(Q:ℝ)*vaughanShortBound Q X T+
    ((k:ℝ)*((k:ℝ)+1)*Real.log (X+1:ℕ))*
      (4*(X:ℝ)/(R:ℝ)+16*Real.sqrt (conductorHarmonicBound Q)*(X:ℝ)/Real.sqrt (T+1:ℕ)+
        4*(Q:ℝ)*conductorHarmonicBound Q*Real.sqrt X)

theorem highConductorBlockBound_nonneg (Q X T R k : ℕ) :
    0 ≤ highConductorBlockBound Q X T R k := by
  have hs:=vaughanShortBound_nonneg Q X T
  have hh:=(conductorHarmonicBound_pos Q).le
  have hl:=log_nat_nonneg (X+1)
  unfold highConductorBlockBound
  positivity

theorem vaughanBilinearBound_doubling (Q X T D : ℕ) (hD : 1 ≤ D) (hQ : 2*D ≤ Q) :
    vaughanBilinearBound (2*D) X T ≤ (D:ℝ)*
      (4*(X:ℝ)/(D:ℝ)+16*Real.sqrt (conductorHarmonicBound Q)*(X:ℝ)/Real.sqrt (T+1:ℕ)+
        4*(Q:ℝ)*conductorHarmonicBound Q*Real.sqrt X) := by
  let H:=conductorHarmonicBound Q
  have hH : 0 ≤ H := (conductorHarmonicBound_pos Q).le
  have hDr : 0 < (D:ℝ) := by exact_mod_cast (show 0 < D by omega)
  have hQr : 2*(D:ℝ) ≤ Q := by exact_mod_cast hQ
  have hz : ((2*D:ℕ):ℝ)^2*(harmonic ((2*D)^2):ℝ) ≤ ((2*D:ℕ):ℝ)^2*H :=
    mul_le_mul_of_nonneg_left (conductor_harmonic_le hQ) (sq_nonneg _)
  have hs : Real.sqrt (((2*D:ℕ):ℝ)^2*(harmonic ((2*D)^2):ℝ)) ≤
      ((2*D:ℕ):ℝ)*Real.sqrt H := by
    apply (Real.sqrt_le_sqrt hz).trans_eq
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Nat.cast_nonneg _)]
  have htail : (((2*D:ℕ):ℝ)^2*H)*(2*Real.sqrt X) ≤
      (D:ℝ)*(4*(Q:ℝ)*H*Real.sqrt X) := by
    calc
      _ = (2*(D:ℝ))*(4*(D:ℝ)*H*Real.sqrt X) := by push_cast; ring
      _ ≤ (Q:ℝ)*(4*(D:ℝ)*H*Real.sqrt X) :=
        mul_le_mul_of_nonneg_right hQr (by positivity)
      _ = _ := by ring
  unfold vaughanBilinearBound
  calc
    _ ≤ 4*(X:ℝ)+(((2*D:ℕ):ℝ)*Real.sqrt H)*(8*(X:ℝ)/Real.sqrt (T+1:ℕ))+
        ((((2*D:ℕ):ℝ)^2*H)*(2*Real.sqrt X)) :=
      add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hs (by positivity)))
        (mul_le_mul_of_nonneg_right hz (by positivity))
    _ ≤ 4*(X:ℝ)+(((2*D:ℕ):ℝ)*Real.sqrt H)*(8*(X:ℝ)/Real.sqrt (T+1:ℕ))+
        (D:ℝ)*(4*(Q:ℝ)*H*Real.sqrt X) := add_le_add le_rfl htail
    _ = _ := by
      change _=(D:ℝ)*(4*(X:ℝ)/(D:ℝ)+16*Real.sqrt H*(X:ℝ)/Real.sqrt (T+1:ℕ)+
        4*(Q:ℝ)*H*Real.sqrt X)
      push_cast
      field_simp
      ring

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_DyadicMeans

section File_OpenAIPrimeGaps_ConductorBounds

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

theorem conductor_doubling_error_le (Q X T k D : ℕ) (hD : 1 ≤ D)
    (hQ : 2*D ≤ Q) (hk : X+1 ≤ 2^k) :
    (∑ d∈Finset.Ioc D (2*D),primitiveErrorMass (X:ℝ) d/(d.totient:ℝ)) ≤
      highConductorBlockBound Q X T D k := by
  have hDr : 0 < (D:ℝ) := by exact_mod_cast (show 0 < D by omega)
  have hdq : ((2*D:ℕ):ℝ) ≤ Q := by exact_mod_cast hQ
  have hsq : (((2*D:ℕ):ℝ)^2) ≤ ((2*D:ℕ):ℝ)*(Q:ℝ) := by
    nlinarith [show (0:ℝ) ≤ ((2*D:ℕ):ℝ) from Nat.cast_nonneg _]
  have hshort : (((2*D:ℕ):ℝ)^2)*vaughanShortBound (2*D) X T ≤
      (D:ℝ)*(2*(Q:ℝ)*vaughanShortBound Q X T) := by
    calc
      _ ≤ (((2*D:ℕ):ℝ)^2)*vaughanShortBound Q X T :=
        mul_le_mul_of_nonneg_left (vaughanShortBound_mono hQ X T) (sq_nonneg _)
      _ ≤ (((2*D:ℕ):ℝ)*(Q:ℝ))*vaughanShortBound Q X T :=
        mul_le_mul_of_nonneg_right hsq (vaughanShortBound_nonneg _ _ _)
      _ = _ := by push_cast; ring
  have hbilin:=vaughanBilinearBound_doubling Q X T D hD hQ
  have hC : 0 ≤ (k:ℝ)*((k:ℝ)+1)*Real.log (X+1:ℕ) := by
    have h:=log_nat_nonneg (X+1)
    positivity
  have h:=(conductor_interval_error_le_vaughan (2*D) X T k D hD hk).trans
    (add_le_add hshort (by
      convert mul_le_mul_of_nonneg_left hbilin hC using 1
      ring))
  apply (mul_le_mul_iff_right₀ hDr).mp
  convert h using 1
  unfold highConductorBlockBound
  ring

theorem highConductorBlockBound_antitone_radius (Q X T k : ℕ) {R D : ℕ}
    (hR : 1 ≤ R) (hRD : R ≤ D) :
    highConductorBlockBound Q X T D k ≤ highConductorBlockBound Q X T R k := by
  have hdiv : 4*(X:ℝ)/(D:ℝ) ≤ 4*(X:ℝ)/(R:ℝ) :=
    div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast (show 0 < R by omega))
      (by exact_mod_cast hRD)
  have hC : 0 ≤ (k:ℝ)*((k:ℝ)+1)*Real.log (X+1:ℕ) := by
    have h:=log_nat_nonneg (X+1)
    positivity
  unfold highConductorBlockBound
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add hdiv le_rfl) le_rfl) hC)

theorem sum_Ioc_dyadic {A : Type*} [AddCommMonoid A] (F : ℕ→A) (r n : ℕ) :
    (∑ d∈Finset.Ioc (2^r) (2^(r+n)),F d)=
      ∑ j∈Finset.range n,∑ d∈Finset.Ioc (2^(r+j)) (2^(r+j+1)),F d := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,←ih]
    exact (Finset.sum_Ioc_consecutive F (show 2^r ≤ 2^(r+n) from
      pow_le_pow_right₀ (by omega) (by omega))
      (show 2^(r+n) ≤ 2^(r+n+1) from pow_le_pow_right₀ (by omega) (by omega))).symm

theorem high_conductor_error_le (X T k r n : ℕ) (hk : X+1 ≤ 2^k) :
    (∑ d∈Finset.Ioc (2^r) (2^(r+n)),primitiveErrorMass (X:ℝ) d/(d.totient:ℝ)) ≤
      (n:ℝ)*highConductorBlockBound (2^(r+n)) X T (2^r) k := by
  rw [sum_Ioc_dyadic]
  calc
    _ ≤ ∑ _j∈Finset.range n,highConductorBlockBound (2^(r+n)) X T (2^r) k := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn:=Finset.mem_range.mp hj
      have hD : 1 ≤ 2^(r+j) := one_le_pow₀ (by omega)
      have hpow : 2^(r+j+1)=2*2^(r+j) := by rw [pow_succ]; omega
      rw [hpow]
      apply (conductor_doubling_error_le (2^(r+n)) X T k (2^(r+j)) hD ?_ hk).trans
      · exact highConductorBlockBound_antitone_radius _ _ _ _ (one_le_pow₀ (by omega))
          (pow_le_pow_right₀ (by omega) (by omega))
      · rw [←hpow]
        exact pow_le_pow_right₀ (by omega) (by omega)
    _ = _ := by simp

theorem endpoint_errors_finite_vaughan_reduction (X T k r n : ℕ) (hk : X+1 ≤ 2^k) :
    (∑ q∈Finset.Icc 1 (2^(r+n)),(endpointError (X:ℝ) q:ℝ)) ≤
      ((∑ d∈Finset.Icc 1 (2^r),primitiveErrorMass (X:ℝ) d/(d.totient:ℝ))+
        (n:ℝ)*highConductorBlockBound (2^(r+n)) X T (2^r) k)*(harmonic (2^(r+n)):ℝ)^2+
      ((2^(r+n):ℕ):ℝ)*(Nat.log 2 X:ℝ)*Real.log (2^(r+n):ℕ) := by
  have hR : 2^r ≤ 2^(r+n) := pow_le_pow_right₀ (by omega) (by omega)
  have hRpos : 1 ≤ 2^r := one_le_pow₀ (by omega)
  have he : Finset.Icc 1 (2^(r+n))=Finset.Icc 1 (2^r)∪Finset.Ioc (2^r) (2^(r+n)) := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_union,Finset.mem_Ioc]
    omega
  have hd : Disjoint (Finset.Icc 1 (2^r)) (Finset.Ioc (2^r) (2^(r+n))) := by
    apply Finset.disjoint_left.mpr
    intro d h1 h2
    have h1':=Finset.mem_Icc.mp h1
    have h2':=Finset.mem_Ioc.mp h2
    omega
  have h:=endpointErrors_le_primitive_weighted_sum (X:ℝ) (2^(r+n))
  simp only [Nat.floor_natCast] at h
  apply h.trans
  rw [he,Finset.sum_union hd]
  exact add_le_add (mul_le_mul_of_nonneg_right
    (add_le_add le_rfl (high_conductor_error_le X T k r n hk)) (sq_nonneg _)) le_rfl

theorem primitiveErrorMass_one (x : ℝ) :
    primitiveErrorMass x 1 =
      |(∑ n∈Finset.Ioc 0 ⌊x⌋₊,ArithmeticFunction.vonMangoldt n)-x| := by
  have hone (n : ℕ) : (1 : DirichletCharacter ℂ 1) (n:ZMod 1)=1 := by
    apply MulChar.one_apply
    exact (ZMod.isUnit_iff_coprime n 1).mpr (by simp)
  have he : primeCharacterPrefix x (1 : DirichletCharacter ℂ 1)=
      ((∑ n∈Finset.Ioc 0 ⌊x⌋₊,ArithmeticFunction.vonMangoldt n):ℝ) := by
    simp only [primeCharacterPrefix,hone,one_mul,Complex.ofReal_sum]
  simp only [primitiveErrorMass,Finset.sum_filter]
  rw [Fintype.sum_unique]
  rw [DirichletCharacter.level_one (default : DirichletCharacter ℂ 1)]
  simp only [DirichletCharacter.isPrimitive_one_level_one,↓reduceIte,primeCharacterError,
    he,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]

theorem PNT_error_le_small_conductor_mass (x : ℝ) {R : ℕ} (hR : 1 ≤ R) :
    |(∑ n∈Finset.Ioc 0 ⌊x⌋₊,ArithmeticFunction.vonMangoldt n)-x| ≤
      ∑ d∈Finset.Icc 1 R,primitiveErrorMass x d/(d.totient:ℝ) := by
  have h := Finset.single_le_sum
    (f:=fun d : ℕ => primitiveErrorMass x d/(d.totient:ℝ))
    (fun d _ => div_nonneg (primitiveErrorMass_nonneg x d) (Nat.cast_nonneg _))
    (Finset.mem_Icc.mpr ⟨le_rfl,hR⟩)
  simpa only [Nat.totient_one,Nat.cast_one,div_one,primitiveErrorMass_one] using h

theorem endpoint_errors_finite_vaughan_reduction_of_le (X T k r n Q : ℕ)
    (hk : X+1 ≤ 2^k) (hQ : Q ≤ 2^(r+n)) :
    (∑ q∈Finset.Icc 1 Q,(endpointError (X:ℝ) q:ℝ)) ≤
      ((∑ d∈Finset.Icc 1 (2^r),primitiveErrorMass (X:ℝ) d/(d.totient:ℝ))+
        (n:ℝ)*highConductorBlockBound (2^(r+n)) X T (2^r) k)*(harmonic (2^(r+n)):ℝ)^2+
      ((2^(r+n):ℕ):ℝ)*(Nat.log 2 X:ℝ)*Real.log (2^(r+n):ℕ) := by
  apply le_trans ?_ (endpoint_errors_finite_vaughan_reduction X T k r n hk)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    have h:=Finset.mem_Icc.mp hq
    exact Finset.mem_Icc.mpr ⟨h.1,h.2.trans hQ⟩
  · intro q _ _
    exact NNReal.coe_nonneg _

theorem endpointError_le_floor (x : ℝ) (q : ℕ) :
    (endpointError x q:ℝ) ≤ (endpointError (⌊x⌋₊:ℝ) q:ℝ)+
      |x-(⌊x⌋₊:ℝ)|/(q.totient:ℝ) := by
  have hb : 0 ≤ (endpointError (⌊x⌋₊:ℝ) q:ℝ)+|x-(⌊x⌋₊:ℝ)|/(q.totient:ℝ) := by
    positivity
  change (endpointError x q:ℝ) ≤
    ((⟨(endpointError (⌊x⌋₊:ℝ) q:ℝ)+|x-(⌊x⌋₊:ℝ)|/(q.totient:ℝ),hb⟩:NNReal):ℝ)
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro c hc
  split_ifs with hcop
  · apply NNReal.coe_le_coe.mp
    change |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient| ≤ _
    calc
      _ ≤ |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-(⌊x⌋₊:ℝ)/q.totient|+
          |(⌊x⌋₊:ℝ)/q.totient-x/q.totient| := abs_sub_le _ _ _
      _ ≤ (endpointError (⌊x⌋₊:ℝ) q:ℝ)+|x-(⌊x⌋₊:ℝ)|/(q.totient:ℝ) := by
        apply add_le_add (endpointClassError_le ⌊x⌋₊ (Finset.mem_range.mp hc) hcop)
        rw [←sub_div,abs_div,abs_of_nonneg (show (0:ℝ) ≤ q.totient from Nat.cast_nonneg _),abs_sub_comm]
  · exact bot_le

theorem sum_endpointError_le_floor (x : ℝ) (Q : ℕ) :
    (∑ q∈Finset.Icc 1 Q,(endpointError x q:ℝ)) ≤
      (∑ q∈Finset.Icc 1 Q,(endpointError (⌊x⌋₊:ℝ) q:ℝ))+
        |x-(⌊x⌋₊:ℝ)| *(harmonic Q:ℝ)^2 := by
  apply (Finset.sum_le_sum (fun q _ => endpointError_le_floor x q)).trans
  rw [Finset.sum_add_distrib]
  apply add_le_add le_rfl
  calc
    _ = |x-(⌊x⌋₊:ℝ)| *(∑ q∈Finset.Icc 1 Q,(1:ℝ)/(q.totient:ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_totient_reciprocal_le Q) (abs_nonneg _)

theorem sum_endpointError_le_floor_add_harmonic {x : ℝ} (hx : 0 ≤ x) (Q : ℕ) :
    (∑ q∈Finset.Icc 1 Q,(endpointError x q:ℝ)) ≤
      (∑ q∈Finset.Icc 1 Q,(endpointError (⌊x⌋₊:ℝ) q:ℝ))+(harmonic Q:ℝ)^2 := by
  apply (sum_endpointError_le_floor x Q).trans
  apply add_le_add le_rfl
  have h1 : 0 ≤ x-(⌊x⌋₊:ℝ) := sub_nonneg.mpr (Nat.floor_le hx)
  have h2 : |x-(⌊x⌋₊:ℝ)| ≤ 1 := by
    rw [abs_of_nonneg h1]
    have h:=Nat.lt_floor_add_one x
    linarith
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h2 (sq_nonneg (harmonic Q:ℝ))

theorem endpoint_errors_real_finite_vaughan_reduction {x : ℝ} (hx : 0 ≤ x)
    (T k r n Q : ℕ) (hk : ⌊x⌋₊+1 ≤ 2^k) (hQ : Q ≤ 2^(r+n)) :
    (∑ q∈Finset.Icc 1 Q,(endpointError x q:ℝ)) ≤
      (((∑ d∈Finset.Icc 1 (2^r),primitiveErrorMass (⌊x⌋₊:ℝ) d/(d.totient:ℝ))+
        (n:ℝ)*highConductorBlockBound (2^(r+n)) ⌊x⌋₊ T (2^r) k)*(harmonic (2^(r+n)):ℝ)^2+
      ((2^(r+n):ℕ):ℝ)*(Nat.log 2 ⌊x⌋₊:ℝ)*Real.log (2^(r+n):ℕ))+(harmonic Q:ℝ)^2 := by
  exact (sum_endpointError_le_floor_add_harmonic hx Q).trans
    (add_le_add (endpoint_errors_finite_vaughan_reduction_of_le ⌊x⌋₊ T k r n Q hk hQ) le_rfl)

open Filter Topology

def SiegelWalfisz : Prop :=
  ∀ A B : ℝ, 0 < A → 0 < B → ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → ∀ d : ℕ, 0 < d → (d:ℝ) ≤ (Real.log x)^B →
      ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
        ‖primeCharacterError x χ‖ ≤ M*x*(Real.log x)^(-A)

theorem primitiveErrorMass_div_le {x M : ℝ} (hM : 0 ≤ M) {d : ℕ} (hd : 0 < d)
    (h : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive → ‖primeCharacterError x χ‖ ≤ M) :
    primitiveErrorMass x d/(d.totient:ℝ) ≤ M := by
  classical
  let : NeZero d := ⟨by omega⟩
  have hphi : 0 < (d.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd
  have hcard : Fintype.card (DirichletCharacter ℂ d) = d.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d
  apply (div_le_iff₀ hphi).mpr
  calc
    _ ≤ ∑ _χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).filter
        DirichletCharacter.IsPrimitive, M := by
      exact Finset.sum_le_sum (fun χ hχ => h χ (Finset.mem_filter.mp hχ).2)
    _ ≤ ∑ _χ : DirichletCharacter ℂ d, M :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => hM)
    _ = _ := by simp [hcard, mul_comm]

theorem small_conductor_mass_le {x M : ℝ} (hM : 0 ≤ M) (R : ℕ)
    (h : ∀ d : ℕ, 0 < d → d ≤ R → ∀ χ : DirichletCharacter ℂ d,
      χ.IsPrimitive → ‖primeCharacterError x χ‖ ≤ M) :
    (∑ d ∈ Finset.Icc 1 R, primitiveErrorMass x d/(d.totient:ℝ)) ≤ (R:ℝ)*M := by
  calc
    _ ≤ ∑ _d ∈ Finset.Icc 1 R, M := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hd0, hdR⟩ := Finset.mem_Icc.mp hd
      exact primitiveErrorMass_div_le hM (by omega) (h d (by omega) hdR)
    _ = _ := by simp

noncomputable def dyadicExponent (x : ℝ) : ℕ := Nat.log 2 ⌊x⌋₊+1

theorem dyadicExponent_mono : Monotone dyadicExponent := by
  intro x y hxy
  exact Nat.add_le_add_right (Nat.log_mono_right (Nat.floor_mono hxy)) 1

theorem dyadicUpper_bounds {x : ℝ} (hx : 1 ≤ x) :
    x < ((2^(dyadicExponent x):ℕ):ℝ) ∧ ((2^(dyadicExponent x):ℕ):ℝ) ≤ 2*x := by
  have hf : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr hx
  have hlo := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊x⌋₊
  have hup := Nat.pow_log_le_self 2 (by omega : ⌊x⌋₊ ≠ 0)
  constructor
  · apply (Nat.lt_floor_add_one x).trans_le
    exact_mod_cast hlo
  · unfold dyadicExponent
    rw [pow_succ]
    push_cast
    have hh : ((2^(Nat.log 2 ⌊x⌋₊):ℕ):ℝ) ≤ x :=
      (by exact_mod_cast hup : ((2^(Nat.log 2 ⌊x⌋₊):ℕ):ℝ) ≤ ⌊x⌋₊).trans
        (Nat.floor_le (by linarith))
    push_cast at hh
    nlinarith

theorem log_add_one_le_twice {X : ℕ} (hX : 2 ≤ X) :
    Real.log (X+1:ℕ) ≤ 2*Real.log (X:ℝ) := by
  have hx : (2:ℝ) ≤ X := by exact_mod_cast hX
  calc
    _ ≤ Real.log ((X:ℝ)^2) := Real.log_le_log (by positivity) (by push_cast; nlinarith)
    _ = _ := by rw [Real.log_pow]; ring

theorem vaughanBinaryExponent_bounds {X : ℕ} (hX : 2 ≤ X) (hL : 1 ≤ Real.log (X:ℝ)) :
    X+1 ≤ 2^(dyadicExponent (X+1:ℕ)) ∧
      (dyadicExponent (X+1:ℕ):ℝ) ≤ 6*Real.log (X:ℝ) := by
  constructor
  · exact_mod_cast (dyadicUpper_bounds (show (1:ℝ) ≤ (X+1:ℕ) by exact_mod_cast (by omega : 1 ≤ X+1))).1.le
  · rw [dyadicExponent, Nat.floor_natCast]
    push_cast
    have hn := Real.natLog_le_logb (X+1) 2
    have hl2 : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hd : Real.log (X+1:ℕ)/Real.log 2 ≤ 4*Real.log (X:ℝ) := by
      apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
      have h := log_add_one_le_twice hX
      nlinarith
    norm_num only [Real.logb, Nat.cast_ofNat] at hn
    linarith

theorem vaughanShortBound_power_le {Q X T : ℕ} (hX : 2 ≤ X)
    (hL : 1 ≤ Real.log (X:ℝ)) (hQX : Q ≤ X)
    (hQ : (Q:ℝ) ≤ 4*(X:ℝ)^(1/2:ℝ))
    (hT : (T:ℝ) ≤ (X:ℝ)^(1/16:ℝ)) :
    vaughanShortBound Q X T ≤ 32*(X:ℝ)^(3/8:ℝ)*(Real.log (X:ℝ))^2 := by
  let x : ℝ := X
  let L : ℝ := Real.log x
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (by omega : 1 ≤ X)
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hL0 : 0 ≤ L := by dsimp [L,x]; linarith
  have htX : (T:ℝ) ≤ x := hT.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1
      (by norm_num : (1/16:ℝ) ≤ 1))
  have htL : Real.log (T:ℝ) ≤ L := log_nat_monotone (by change (T:ℝ) ≤ (X:ℝ) at htX; exact_mod_cast htX)
  have hqL : Real.log (Q:ℝ) ≤ L := log_nat_monotone hQX
  have hxxL : Real.log (X+1:ℕ) ≤ 2*L := log_add_one_le_twice hX
  have hqroot : Real.sqrt Q ≤ 2*x^(1/4:ℝ) := by
    apply (Real.sqrt_le_sqrt hQ).trans_eq
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), Real.sqrt_eq_rpow,
      Real.sqrt_eq_rpow, ←Real.rpow_mul hx.le]
    norm_num
  have hK : Real.sqrt Q*(1+Real.log Q) ≤ 4*x^(1/4:ℝ)*L := by
    calc
      _ ≤ (2*x^(1/4:ℝ))*(2*L) := mul_le_mul hqroot (by dsimp [L,x] at *; linarith)
        (by have hh:=log_nat_nonneg Q; linarith) (by positivity)
      _ = _ := by ring
  have ht2 : ((T*T:ℕ):ℝ) ≤ x^(1/8:ℝ) := by
    calc
      _ = (T:ℝ)^2 := by push_cast; ring
      _ ≤ (x^(1/16:ℝ))^2 := pow_le_pow_left₀ (Nat.cast_nonneg T) hT 2
      _ = _ := by rw [←Real.rpow_natCast,←Real.rpow_mul hx.le]; norm_num
  have httL : Real.log (T*T:ℕ) ≤ 2*L := by
    calc
      _ = 2*Real.log (T:ℝ) := by rw [Nat.cast_mul, ←pow_two,Real.log_pow]; norm_num
      _ ≤ _ := by linarith
  have he1 : x^(1/16:ℝ) ≤ x^(3/8:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have he2 : x^(5/16:ℝ) ≤ x^(3/8:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have h1 : (T:ℝ)*Real.log T ≤ x^(3/8:ℝ)*L^2 := by
    calc
      _ ≤ x^(3/8:ℝ)*L := mul_le_mul (hT.trans he1) htL (log_nat_nonneg _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by dsimp [L,x] at *; nlinarith) (by positivity)
  have h2 : (T:ℝ)*(2*Real.log (X+1:ℕ)*(Real.sqrt Q*(1+Real.log Q))) ≤
      16*x^(3/8:ℝ)*L^2 := by
    calc
      _ ≤ x^(1/16:ℝ)*(2*(2*L)*(4*x^(1/4:ℝ)*L)) := by gcongr
      _ = 16*x^(5/16:ℝ)*L^2 := by
        rw [show (5/16:ℝ)=1/16+1/4 by norm_num,Real.rpow_add hx]; ring
      _ ≤ _ := by gcongr
  have h3 : (((T*T:ℕ):ℝ)*Real.log (T*T:ℕ))*(Real.sqrt Q*(1+Real.log Q)) ≤
      8*x^(3/8:ℝ)*L^2 := by
    calc
      _ ≤ (x^(1/8:ℝ)*(2*L))*(4*x^(1/4:ℝ)*L) := by gcongr
      _ = _ := by rw [show (3/8:ℝ)=1/8+1/4 by norm_num,Real.rpow_add hx]; ring
  unfold vaughanShortBound
  dsimp only
  change _ ≤ 32*x^(3/8:ℝ)*L^2
  nlinarith [mul_nonneg (Real.rpow_nonneg hx.le (3/8:ℝ)) (sq_nonneg L)]

theorem conductorHarmonicBound_le {Q X : ℕ} (hQ : Q ≤ X)
    (hL : 1 ≤ Real.log (X:ℝ)) :
    conductorHarmonicBound Q ≤ 3*Real.log (X:ℝ) := by
  unfold conductorHarmonicBound
  rw [Nat.cast_pow,Real.log_pow]
  have h := log_nat_monotone hQ
  norm_num only [Nat.cast_ofNat]
  linarith

theorem sqrt_conductorHarmonicBound_le {Q X : ℕ} (hQ : Q ≤ X)
    (hL : 1 ≤ Real.log (X:ℝ)) :
    Real.sqrt (conductorHarmonicBound Q) ≤ 2*Real.log (X:ℝ) := by
  apply (Real.sqrt_le_sqrt (conductorHarmonicBound_le hQ hL)).trans
  apply (Real.sqrt_le_left (by linarith)).mpr
  nlinarith

theorem rpow_absorption {x L a b c : ℝ} (hx : 0 < x) (hL : 0 < L)
    (h : L^a ≤ x^b) : x^(1-b)*L^c ≤ x*L^(c-a) := by
  calc
    _ = (x^(1-b)*L^(c-a))*L^a := by
      rw [mul_assoc,←Real.rpow_add hL,sub_add_cancel]
    _ ≤ (x^(1-b)*L^(c-a))*x^b :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by
      rw [mul_right_comm,←Real.rpow_add hx,sub_add_cancel,Real.rpow_one]

theorem rpow_absorption_of_exponents {x L a b a' b' c : ℝ}
    (hx : 1 ≤ x) (hL : 1 ≤ L) (h : L^a ≤ x^b) (ha : a' ≤ a) (hb : b ≤ b') :
    x^(1-b')*L^c ≤ x*L^(c-a') :=
  rpow_absorption (lt_of_lt_of_le zero_lt_one hx) (lt_of_lt_of_le zero_lt_one hL)
    ((Real.rpow_le_rpow_of_exponent_le hL ha).trans
      (h.trans (Real.rpow_le_rpow_of_exponent_le hx hb)))

theorem eventually_log_rpow_le_rpow (a : ℝ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop, (Real.log x)^a ≤ x^s := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop a hs).bound (by norm_num : (0:ℝ)<1),
    eventually_ge_atTop (1:ℝ)] with x h hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx) _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0≤x) _),one_mul] using h

theorem highConductorBlockBound_log_le {Q X T R k : ℕ} {A : ℝ}
    (hA : 0 < A) (hX : 2 ≤ X) (hL : 1 ≤ Real.log (X:ℝ)) (hQX : Q ≤ X)
    (hQ : (Q:ℝ) ≤ 4*(X:ℝ)^(1/2:ℝ)*(Real.log (X:ℝ))^(-A-10))
    (hR : (Real.log (X:ℝ))^(A+10) ≤ (R:ℝ))
    (hk : (k:ℝ) ≤ 6*Real.log (X:ℝ))
    (hT : (T:ℝ) ≤ (X:ℝ)^(1/16:ℝ))
    (hTroot : (X:ℝ)^(1/32:ℝ) ≤ Real.sqrt (T+1:ℕ))
    (hpower : (Real.log (X:ℝ))^(A+10) ≤ (X:ℝ)^(1/32:ℝ)) :
    highConductorBlockBound Q X T R k ≤
      8000*(X:ℝ)*(Real.log (X:ℝ))^(-A-3) := by
  let x : ℝ := X
  let L : ℝ := Real.log x
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (by omega : 1 ≤ X)
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hL1 : 1 ≤ L := hL
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hneg : L^(-A-10) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL1
      (show -A-10 ≤ 0 by linarith)
  have hQweak : (Q:ℝ) ≤ 4*x^(1/2:ℝ) := by
    apply hQ.trans
    exact (mul_le_mul_of_nonneg_left hneg (by positivity)).trans_eq (mul_one _)
  have hsnonneg := vaughanShortBound_nonneg Q X T
  have hHnonneg := (conductorHarmonicBound_pos Q).le
  have hshort := vaughanShortBound_power_le hX hL hQX hQweak hT
  have hshortAbs : x^(7/8:ℝ)*L^2 ≤ x*L^(-A-3) := by
    convert rpow_absorption_of_exponents (c:=2) hx1 hL1 hpower
      (show A+5 ≤ A+10 by linarith) (show (1/32:ℝ) ≤ 1/8 by norm_num) using 1 <;> norm_num
    all_goals ring_nf
    all_goals simp
  have hshortTotal : 2*(Q:ℝ)*vaughanShortBound Q X T ≤ 256*x*L^(-A-3) := by
    calc
      _ ≤ 2*(4*x^(1/2:ℝ))*(32*x^(3/8:ℝ)*L^2) := by gcongr
      _ = 256*(x^(7/8:ℝ)*L^2) := by
        rw [show (7/8:ℝ)=1/2+3/8 by norm_num, Real.rpow_add hx]; ring
      _ ≤ _ := by nlinarith [hshortAbs]
  have hcoef : (k:ℝ)*((k:ℝ)+1)*Real.log (X+1:ℕ) ≤ 84*L^3 := by
    calc
      _ ≤ (6*L)*(7*L)*(2*L) := by
        gcongr
        · dsimp [L,x] at *; linarith
        · exact log_add_one_le_twice hX
      _ = _ := by ring
  have hRpos : 0 < (R:ℝ) := (Real.rpow_pos_of_pos hL0 _).trans_le hR
  have hb1 : 4*x/(R:ℝ) ≤ 4*x*L^(-A-6) := by
    calc
      _ ≤ 4*x/L^(A+10) := div_le_div_of_nonneg_left (by positivity)
        (Real.rpow_pos_of_pos hL0 _) hR
      _ = 4*x*L^(-A-10) := by
        rw [show -A-10=-(A+10) by ring,Real.rpow_neg hL0.le,div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) (by positivity)
  have habs2 : x^(31/32:ℝ)*L ≤ x*L^(-A-6) := by
    convert rpow_absorption_of_exponents (c:=1) hx1 hL1 hpower
      (show A+7 ≤ A+10 by linarith) (le_refl (1/32:ℝ)) using 1 <;> norm_num
    all_goals ring_nf
    all_goals simp
  have hb2 : 16*Real.sqrt (conductorHarmonicBound Q)*x/Real.sqrt (T+1:ℕ) ≤
      32*x*L^(-A-6) := by
    calc
      _ ≤ 16*(2*L)*x/x^(1/32:ℝ) := by
        apply div_le_div₀ (by positivity) ?_ (Real.rpow_pos_of_pos hx _) hTroot
        gcongr
        exact sqrt_conductorHarmonicBound_le hQX hL
      _ = 32*(x^(31/32:ℝ)*L) := by
        rw [show (31/32:ℝ)=1-1/32 by norm_num,Real.rpow_sub hx,Real.rpow_one]
        ring
      _ ≤ _ := by nlinarith [habs2]
  have hb3 : 4*(Q:ℝ)*conductorHarmonicBound Q*Real.sqrt X ≤ 48*x*L^(-A-6) := by
    calc
      _ ≤ 4*(4*x^(1/2:ℝ)*L^(-A-10))*(3*L)*x^(1/2:ℝ) := by
        rw [Real.sqrt_eq_rpow]
        gcongr
        exact conductorHarmonicBound_le hQX hL
      _ = 48*x*L^(-A-9) := by
        rw [show -A-9=(-A-10)+1 by ring,Real.rpow_add hL0,Real.rpow_one]
        have hh : x^(1/2:ℝ)*x^(1/2:ℝ)=x := by rw [←Real.rpow_add hx]; norm_num
        calc
          _ = 48*(x^(1/2:ℝ)*x^(1/2:ℝ))*(L^(-A-10)*L) := by ring
          _ = _ := by rw [hh]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) (by positivity)
  have hbracket := add_le_add (add_le_add hb1 hb2) hb3
  have hlarge : ((k:ℝ)*((k:ℝ)+1)*Real.log (X+1:ℕ))*
      (4*x/(R:ℝ)+16*Real.sqrt (conductorHarmonicBound Q)*x/Real.sqrt (T+1:ℕ)+
        4*(Q:ℝ)*conductorHarmonicBound Q*Real.sqrt X) ≤ 7056*x*L^(-A-3) := by
    calc
      _ ≤ (84*L^3)*(84*x*L^(-A-6)) := by
        apply mul_le_mul hcoef (by linarith [hbracket]) (by positivity) (by positivity)
      _ = _ := by
        rw [show -A-3=(-A-6)+3 by ring,Real.rpow_add hL0]
        norm_num
        ring
  unfold highConductorBlockBound
  change _ ≤ 8000*x*L^(-A-3)
  nlinarith [mul_pos hx (Real.rpow_pos_of_pos hL0 (-A-3))]

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_ConductorBounds

section File_OpenAIPrimeGaps_LogParameters

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

open Filter Topology

theorem exists_vaughan_log_parameters {A : ℝ} (hA : 0 < A) {X : ℕ}
    (hX : 16 ≤ X) (hL : 2 ≤ Real.log (X:ℝ))
    (hpower : (Real.log (X:ℝ))^(A+10) ≤ (X:ℝ)^(1/32:ℝ)) :
    ∃ T k r n : ℕ,
      X+1 ≤ 2^k ∧
      2*(X:ℝ)^(1/2:ℝ)*(Real.log (X:ℝ))^(-A-10) ≤ ((2^(r+n):ℕ):ℝ) ∧
      2^(r+n) ≤ X ∧
      ((2^(r+n):ℕ):ℝ) ≤ 4*(X:ℝ)^(1/2:ℝ)*(Real.log (X:ℝ))^(-A-10) ∧
      (Real.log (X:ℝ))^(A+10) ≤ ((2^r:ℕ):ℝ) ∧
      ((2^r:ℕ):ℝ) ≤ 2*(Real.log (X:ℝ))^(A+10) ∧
      (n:ℝ) ≤ 6*Real.log (X:ℝ) ∧
      (k:ℝ) ≤ 6*Real.log (X:ℝ) ∧
      (T:ℝ) ≤ (X:ℝ)^(1/16:ℝ) ∧
      (X:ℝ)^(1/32:ℝ) ≤ Real.sqrt (T+1:ℕ) := by
  let x : ℝ := X
  let L : ℝ := Real.log x
  let B : ℝ := A+10
  let y : ℝ := 2*x^(1/2:ℝ)*L^(-B)
  let T : ℕ := ⌊x^(1/16:ℝ)⌋₊
  let k : ℕ := dyadicExponent (X+1:ℕ)
  let r : ℕ := dyadicExponent (L^B)
  let m : ℕ := dyadicExponent y
  have hx16 : (16:ℝ) ≤ x := by dsimp [x]; exact_mod_cast hX
  have hx1 : 1 ≤ x := by linarith
  have hx : 0 < x := by linarith
  have hL1 : 1 ≤ L := by dsimp [L,x]; linarith
  have hL0 : 0 < L := by linarith
  have hB : 0 < B := by dsimp [B]; linarith
  have hLB : 1 ≤ L^B := Real.one_le_rpow hL1 hB.le
  have hneg : L^(-B) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL1 (neg_nonpos.mpr hB.le)
  have hLL : L^B*L^B ≤ x^(1/2:ℝ) := by
    calc
      _ ≤ x^(1/32:ℝ)*x^(1/32:ℝ) := mul_le_mul hpower hpower (by positivity) (by positivity)
      _ = x^(1/16:ℝ) := by rw [←Real.rpow_add hx]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have heB : -B = -A-10 := by dsimp [B]; ring
  have hyeq : y = 2*(X:ℝ)^(1/2:ℝ)*(Real.log (X:ℝ))^(-A-10) := by
    simp only [y,heB,L,x]
  have hLy : L^B ≤ y := by
    have he : L^B*L^(-B)=1 := by rw [←Real.rpow_add hL0]; simp
    calc
      _ = (L^B*L^B)*L^(-B) := by rw [mul_assoc,he,mul_one]
      _ ≤ x^(1/2:ℝ)*L^(-B) := mul_le_mul_of_nonneg_right hLL (by positivity)
      _ ≤ y := by dsimp [y]; nlinarith [mul_nonneg (Real.rpow_nonneg hx.le (1/2:ℝ)) (Real.rpow_nonneg hL0.le (-B))]
  have hy1 : 1 ≤ y := hLB.trans hLy
  have hry : r ≤ m := dyadicExponent_mono hLy
  have hrbounds := dyadicUpper_bounds hLB
  have hmbounds := dyadicUpper_bounds hy1
  have hsqrt : 4*x^(1/2:ℝ) ≤ x := by
    rw [←Real.sqrt_eq_rpow]
    have hs : Real.sqrt x ≤ x/4 := by
      apply (Real.sqrt_le_left (by positivity)).mpr
      nlinarith
    linarith
  have hymX : 2*y ≤ x := by
    calc
      _ = 4*x^(1/2:ℝ)*L^(-B) := by dsimp [y]; ring
      _ ≤ 4*x^(1/2:ℝ) := (mul_le_mul_of_nonneg_left hneg (by positivity)).trans_eq (mul_one _)
      _ ≤ _ := hsqrt
  have hmX : 2^m ≤ X := by
    have hh : ((2^m:ℕ):ℝ) ≤ (X:ℝ) := hmbounds.2.trans hymX
    exact_mod_cast hh
  have hymk : y ≤ (X+1:ℕ) := by
    have hy0 : 0 ≤ y := by positivity
    have hyx : y ≤ x := by linarith
    push_cast
    change y ≤ x+1
    linarith
  have hmk : m ≤ k := dyadicExponent_mono hymk
  have hkbounds := vaughanBinaryExponent_bounds (show 2 ≤ X by omega) (show 1 ≤ Real.log (X:ℝ) by linarith)
  have hrnm : r+(m-r)=m := Nat.add_sub_of_le hry
  refine ⟨T,k,r,m-r,hkbounds.1,?_,?_,?_,?_,?_,?_,hkbounds.2,?_,?_⟩
  · rw [hrnm,←hyeq]
    exact hmbounds.1.le
  · simpa only [hrnm] using hmX
  · rw [hrnm]
    calc
      _ ≤ 2*y := hmbounds.2
      _ = _ := by rw [hyeq]; ring
  · exact hrbounds.1.le
  · exact hrbounds.2
  · exact (by exact_mod_cast (Nat.sub_le m r).trans hmk : ((m-r:ℕ):ℝ) ≤ k).trans hkbounds.2
  · exact Nat.floor_le (Real.rpow_nonneg hx.le _)
  · have ht := (Nat.lt_floor_add_one (x^(1/16:ℝ))).le
    have hh := Real.sqrt_le_sqrt ht
    change Real.sqrt (x^(1/16:ℝ)) ≤ Real.sqrt ((T:ℝ)+1) at hh
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hx.le] at hh
    norm_num at hh
    simpa only [Nat.cast_add,Nat.cast_one] using hh

theorem endpoint_errors_nat_log_bound {A M : ℝ} (hA : 0 < A) (hM : 0 ≤ M)
    {X Q : ℕ} (hX : 16 ≤ X) (hL : 2 ≤ Real.log (X:ℝ))
    (hpower : (Real.log (X:ℝ))^(A+10) ≤ (X:ℝ)^(1/32:ℝ))
    (hQ : (Q:ℝ) ≤ 2*(X:ℝ)^(1/2:ℝ)*(Real.log (X:ℝ))^(-A-10))
    (hsmall : ∀ d : ℕ, 0 < d → (d:ℝ) ≤ (Real.log (X:ℝ))^(A+11) →
      ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
        ‖primeCharacterError (X:ℝ) χ‖ ≤ M*(X:ℝ)*(Real.log (X:ℝ))^(-2*A-14)) :
    (∑ q∈Finset.Icc 1 Q,(endpointError (X:ℝ) q:ℝ)) ≤
      (8*M+192024)*(X:ℝ)*(Real.log (X:ℝ))^(-A) := by
  obtain ⟨T,k,r,n,hk,hcover,hPX,hP,hRlo,hRhi,hn,hkL,hT,hTroot⟩ :=
    exists_vaughan_log_parameters hA hX hL hpower
  let P : ℕ := 2^(r+n)
  let R : ℕ := 2^r
  let x : ℝ := X
  let L : ℝ := Real.log x
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (by omega : 1 ≤ X)
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hL1 : 1 ≤ L := by dsimp [L,x]; linarith
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hQP : Q ≤ P := by
    change Q ≤ 2^(r+n)
    exact_mod_cast hQ.trans hcover
  have hH : (harmonic P:ℝ) ≤ 2*L := harmonic_le_twice_log hPX hL1
  have hH2 : (harmonic P:ℝ)^2 ≤ 4*L^2 := by nlinarith [harmonic_real_nonneg P]
  have hsmallR : (∑ d∈Finset.Icc 1 R,primitiveErrorMass x d/(d.totient:ℝ)) ≤
      (R:ℝ)*(M*x*L^(-2*A-14)) := by
    apply small_conductor_mass_le (by positivity)
    intro d hd hdR χ hχ
    apply hsmall d hd ?_ χ hχ
    calc
      (d:ℝ) ≤ R := by exact_mod_cast hdR
      _ ≤ 2*L^(A+10) := hRhi
      _ ≤ L*L^(A+10) := mul_le_mul_of_nonneg_right hL (by positivity)
      _ = L^(A+11) := by rw [show A+11=1+(A+10) by ring,Real.rpow_add hL0 1 (A+10),Real.rpow_one]
  have hsmallTotal : (∑ d∈Finset.Icc 1 R,primitiveErrorMass x d/(d.totient:ℝ)) *
      (harmonic P:ℝ)^2 ≤ 8*M*x*L^(-A) := by
    calc
      _ ≤ (2*L^(A+10)*(M*x*L^(-2*A-14)))*(4*L^2) := by
        apply mul_le_mul (hsmallR.trans (mul_le_mul_of_nonneg_right hRhi (by positivity))) hH2
          (sq_nonneg _) (by positivity)
      _ = 8*M*x*L^(-A-2) := by
        conv_rhs => rw [show -A-2=(A+10)+(-2*A-14)+2 by ring,
          Real.rpow_add hL0,Real.rpow_add hL0,Real.rpow_two]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) (by positivity)
  have hhi := highConductorBlockBound_log_le hA (show 2 ≤ X by omega) hL1 hPX
    hP hRlo hkL hT hTroot hpower
  have hhighTotal : ((n:ℝ)*highConductorBlockBound P X T R k)*(harmonic P:ℝ)^2 ≤
      192000*x*L^(-A) := by
    calc
      _ ≤ ((6*L)*(8000*x*L^(-A-3)))*(4*L^2) := by
        apply mul_le_mul (mul_le_mul hn hhi (highConductorBlockBound_nonneg _ _ _ _ _) (by positivity))
          hH2 (sq_nonneg _) (by positivity)
      _ = _ := by
        conv_rhs => rw [show -A=(-A-3)+1+2 by ring,Real.rpow_add hL0,Real.rpow_add hL0,
          Real.rpow_one,Real.rpow_two]
        ring
  have hlog2 : (Nat.log 2 X:ℝ) ≤ 6*L := by
    have hmono : Nat.log 2 X ≤ dyadicExponent (X+1:ℕ) := by
      unfold dyadicExponent
      rw [Nat.floor_natCast]
      exact (Nat.log_mono_right (Nat.le_succ X)).trans (Nat.le_succ _)
    exact (by exact_mod_cast hmono : (Nat.log 2 X:ℝ) ≤ (dyadicExponent (X+1:ℕ):ℝ)).trans
      (vaughanBinaryExponent_bounds (show 2 ≤ X by omega) hL1).2
  have hlogP : Real.log (P:ℝ) ≤ L := log_nat_monotone hPX
  have hcost : (P:ℝ)*(Nat.log 2 X:ℝ)*Real.log P ≤ 24*x*L^(-A) := by
    calc
      _ ≤ (4*x^(1/2:ℝ)*L^(-A-10))*(6*L)*L := by
        gcongr
      _ = 24*x^(1/2:ℝ)*L^(-A-8) := by
        rw [show -A-8=(-A-10)+1+1 by ring,Real.rpow_add hL0,Real.rpow_add hL0,Real.rpow_one]
        ring
      _ ≤ _ := by
        have hsx : x^(1/2:ℝ) ≤ x := by
          simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le hx1
            (by norm_num : (1/2:ℝ) ≤ 1))
        apply mul_le_mul (mul_le_mul_of_nonneg_left hsx (by norm_num : (0:ℝ) ≤ 24))
          (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) (by positivity) (by positivity)
  have hfinite := endpoint_errors_finite_vaughan_reduction_of_le X T k r n Q hk hQP
  apply hfinite.trans
  change ((∑ d∈Finset.Icc 1 R,primitiveErrorMass x d/(d.totient:ℝ))+
    (n:ℝ)*highConductorBlockBound P X T R k)*(harmonic P:ℝ)^2+
      (P:ℝ)*(Nat.log 2 X:ℝ)*Real.log P ≤ (8*M+192024)*x*L^(-A)
  rw [add_mul]
  nlinarith [hsmallTotal,hhighTotal,hcost]

theorem endpoint_errors_real_log_bound {A M x : ℝ} (hA : 0 < A) (hM : 0 ≤ M)
    (hx : 0 ≤ x) (hX : 16 ≤ ⌊x⌋₊) (hL : 2 ≤ Real.log (⌊x⌋₊:ℝ))
    (hpower : (Real.log (⌊x⌋₊:ℝ))^(A+10) ≤ (⌊x⌋₊:ℝ)^(1/32:ℝ))
    (hsmall : ∀ d : ℕ, 0 < d → (d:ℝ) ≤ (Real.log (⌊x⌋₊:ℝ))^(A+11) →
      ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
        ‖primeCharacterError (⌊x⌋₊:ℝ) χ‖ ≤ M*(⌊x⌋₊:ℝ)*(Real.log (⌊x⌋₊:ℝ))^(-2*A-14)) :
    (∑ q∈Finset.Icc 1 ⌊x^(1/2:ℝ)*(Real.log x)^(-(A+10))⌋₊,(endpointError x q:ℝ)) ≤
      ((8*M+192028)*(2:ℝ)^A)*x*(Real.log x)^(-A) := by
  let X : ℕ := ⌊x⌋₊
  let Q : ℕ := ⌊x^(1/2:ℝ)*(Real.log x)^(-(A+10))⌋₊
  let L : ℝ := Real.log (X:ℝ)
  have hX16 : (16:ℝ) ≤ X := by
    change (16:ℝ) ≤ (⌊x⌋₊:ℝ)
    exact_mod_cast hX
  have hX1 : (1:ℝ) ≤ X := by linarith
  have hX0 : (0:ℝ) < X := by linarith
  have hfloor : (X:ℝ) ≤ x := Nat.floor_le hx
  have hceil : x < (X:ℝ)+1 := Nat.lt_floor_add_one x
  have hL1 : 1 ≤ L := by dsimp [L,X]; linarith
  have hL0 : 0 < L := by linarith
  have hloglo : L ≤ Real.log x := Real.log_le_log hX0 hfloor
  have hlogx0 : 0 < Real.log x := hL0.trans_le hloglo
  have hloghi : Real.log x ≤ 2*L :=
    calc
      _ ≤ Real.log (X+1:ℕ) := Real.log_le_log (hX0.trans_le hfloor) (by push_cast; linarith)
      _ ≤ _ := log_add_one_le_twice (by omega)
  have hroot : x^(1/2:ℝ) ≤ 2*(X:ℝ)^(1/2:ℝ) := by
    rw [←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow]
    calc
      _ ≤ Real.sqrt (4*(X:ℝ)) := Real.sqrt_le_sqrt (by linarith)
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]; norm_num
  have hQ : (Q:ℝ) ≤ 2*(X:ℝ)^(1/2:ℝ)*L^(-A-10) := by
    calc
      _ ≤ x^(1/2:ℝ)*(Real.log x)^(-(A+10)) := Nat.floor_le (by positivity)
      _ ≤ (2*(X:ℝ)^(1/2:ℝ))*L^(-(A+10)) := mul_le_mul hroot
        (Real.rpow_le_rpow_of_nonpos hL0 hloglo (by linarith)) (by positivity) (by positivity)
      _ = _ := by congr 1; congr 1; ring
  have hneg : L^(-A-10) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL1
      (show -A-10 ≤ 0 by linarith)
  have hQX : Q ≤ X := by
    have hrootsmall : 2*(X:ℝ)^(1/2:ℝ) ≤ X := by
      rw [←Real.sqrt_eq_rpow]
      have hs : Real.sqrt (X:ℝ) ≤ (X:ℝ)/2 := by
        apply (Real.sqrt_le_left (by positivity)).mpr
        nlinarith
      linarith
    have hh₁ : 2*(X:ℝ)^(1/2:ℝ)*L^(-A-10) ≤ 2*(X:ℝ)^(1/2:ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hneg
        (by positivity : 0 ≤ 2*(X:ℝ)^(1/2:ℝ))
    have hh : (Q:ℝ) ≤ X := hQ.trans (hh₁.trans hrootsmall)
    exact_mod_cast hh
  have hnat := endpoint_errors_nat_log_bound hA hM hX hL hpower hQ hsmall
  have hH : (harmonic Q:ℝ) ≤ 2*L := harmonic_le_twice_log hQX hL1
  have habs : L^2 ≤ (X:ℝ)*L^(-A) := by
    convert rpow_absorption_of_exponents (c:=2) hX1 hL1 hpower
      (show A+2 ≤ A+10 by linarith) (show (1/32:ℝ) ≤ 1 by norm_num) using 1 <;> norm_num
  have htotal : (∑ q∈Finset.Icc 1 Q,(endpointError x q:ℝ)) ≤
      (8*M+192028)*(X:ℝ)*L^(-A) := by
    have hh := sum_endpointError_le_floor_add_harmonic hx Q
    have hH2 : (harmonic Q:ℝ)^2 ≤ 4*L^2 := by nlinarith [harmonic_real_nonneg Q]
    nlinarith [hnat,hh,habs,hH2]
  have hlogscale : L^(-A) ≤ (2:ℝ)^A*(Real.log x)^(-A) := by
    calc
      _ ≤ (Real.log x/2)^(-A) := Real.rpow_le_rpow_of_nonpos (by linarith)
        (by linarith) (by linarith)
      _ = _ := by
        rw [Real.div_rpow (by linarith : 0 ≤ Real.log x) (by norm_num : (0:ℝ) ≤ 2),
          Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),div_inv_eq_mul]
        ring
  apply htotal.trans
  calc
    _ ≤ (8*M+192028)*x*((2:ℝ)^A*(Real.log x)^(-A)) := by gcongr
    _ = _ := by ring

theorem bombieriVinogradov_of_siegelWalfisz (hs : SiegelWalfisz) : BombieriVinogradov := by
  intro A hA
  obtain ⟨M,hM,x₀,hx₀,hSW⟩ := hs (2*A+14) (A+11) (by linarith) (by linarith)
  refine ⟨A+10,by linarith,(8*M+192028)*(2:ℝ)^A,by positivity,?_⟩
  have hf : Tendsto (fun x : ℝ => (⌊x⌋₊:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nat_floor_atTop
  have he : ∀ᶠ x : ℝ in atTop,
      (∑ q∈Finset.Icc 1 ⌊x^(1/2:ℝ)*(Real.log x)^(-(A+10))⌋₊,(endpointError x q:ℝ)) ≤
        ((8*M+192028)*(2:ℝ)^A)*x*(Real.log x)^(-A) := by
    filter_upwards [eventually_ge_atTop (0:ℝ),
      tendsto_nat_floor_atTop.eventually (eventually_ge_atTop (16:ℕ)),
      (Real.tendsto_log_atTop.comp hf).eventually_ge_atTop 2,
      hf.eventually_ge_atTop x₀,
      hf.eventually (eventually_log_rpow_le_rpow (A+10) (by norm_num : (0:ℝ)<1/32))]
      with x hx hX hL hxsw hp
    apply endpoint_errors_real_log_bound hA hM.le hx hX hL hp
    intro d hd hdL χ hχ
    convert hSW (⌊x⌋₊:ℝ) hxsw d hd hdL χ hχ using 1
    congr 1
    congr 1
    ring
  obtain ⟨z,hz⟩ := eventually_atTop.mp he
  refine ⟨max z 2,by linarith [le_max_right z (2:ℝ)],?_⟩
  intro x hx
  exact hz x ((le_max_left z (2:ℝ)).trans hx)

open Complex Filter Topology

noncomputable def poleRemovedL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q else χ.LFunction

noncomputable def primeLogDerivativeRegular {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -deriv (poleRemovedL χ) s / poleRemovedL χ s

theorem poleRemovedL_differentiable {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : Differentiable ℂ (poleRemovedL χ) := by
  unfold poleRemovedL
  split_ifs with hχ
  · exact DirichletCharacter.differentiable_LFunctionTrivChar₁ q
  · exact DirichletCharacter.differentiable_LFunction hχ

theorem poleRemovedL_ne_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 ≤ s.re) :
    poleRemovedL χ s ≠ 0 := by
  unfold poleRemovedL
  split_ifs with hχ
  · rcases eq_or_ne s 1 with rfl | hs1
    · exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q
    · rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1]
      refine mul_ne_zero (sub_ne_zero.mpr hs1) ?_
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re 1 (.inr hs1) hs
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs

theorem primeLogDerivativeRegular_analyticAt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : poleRemovedL χ s ≠ 0) :
    AnalyticAt ℂ (primeLogDerivativeRegular χ) s := by
  have h := (poleRemovedL_differentiable χ).analyticAt s
  exact h.deriv.neg.div h hs

theorem primeLogDerivativeRegular_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    primeLogDerivativeRegular χ s =
      LSeries (fun n : ℕ => χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) s -
        (if χ = 1 then 1 / (s - 1) else 0) := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hL := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  change LSeries (fun n : ℕ => χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
    -deriv (LSeries (fun n : ℕ => χ (n : ZMod q))) s /
      LSeries (fun n : ℕ => χ (n : ZMod q)) s at hL
  rw [hL, ← DirichletCharacter.LFunction_eq_LSeries χ hs,
    ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs]
  by_cases hχ : χ = 1
  · subst χ
    have hn := DirichletCharacter.LFunction_ne_zero_of_one_le_re
      (1 : DirichletCharacter ℂ q) (.inr hs1) hs.le
    simp only [primeLogDerivativeRegular, poleRemovedL, ↓reduceIte]
    rw [DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one q hs1,
      DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1]
    change -((s-1)*deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s +
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s) /
      ((s-1)*DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s) = _
    field_simp
    ring
  · simp [primeLogDerivativeRegular, poleRemovedL, hχ]

theorem poleRemovedL_fixed_height_strip {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ, 1-δ ≤ s.re → |s.im| ≤ T →
      poleRemovedL χ s ≠ 0 := by
  let K : Set ℂ := (fun t : ℝ => (1 : ℂ)+(t:ℂ)*I) '' Set.Icc (-T) T
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hO : IsOpen {s : ℂ | poleRemovedL χ s ≠ 0} :=
    isOpen_ne_fun (poleRemovedL_differentiable χ).continuous continuous_const
  have hKO : K ⊆ {s : ℂ | poleRemovedL χ s ≠ 0} := by
    rintro s ⟨t, ht, rfl⟩
    exact poleRemovedL_ne_zero χ (by simp)
  obtain ⟨ε, hε, hεK⟩ := hK.exists_thickening_subset_open hO hKO
  refine ⟨ε/2, by positivity, ?_⟩
  intro s hs ht
  by_cases hs1 : 1 ≤ s.re
  · exact poleRemovedL_ne_zero χ hs1
  apply hεK
  apply Metric.mem_thickening_iff.mpr
  refine ⟨1+(s.im:ℂ)*I, ⟨s.im, abs_le.mp ht, rfl⟩, ?_⟩
  have hd : dist s (1+(s.im:ℂ)*I) = |s.re-1| := by
    rw [dist_eq_norm]
    have he : s-(1+(s.im:ℂ)*I) = ((s.re-1:ℝ):ℂ) := by
      apply Complex.ext <;> simp
    rw [he, Complex.norm_real, Real.norm_eq_abs]
  rw [hd, abs_of_nonpos (by linarith)]
  linarith

theorem primeLogDerivativeRegular_fixed_height_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧ ∀ s : ℂ,
      1-δ ≤ s.re → s.re ≤ 2 → |s.im| ≤ T →
        AnalyticAt ℂ (primeLogDerivativeRegular χ) s ∧
          ‖primeLogDerivativeRegular χ s‖ ≤ M := by
  obtain ⟨δ, hδ, hn⟩ := poleRemovedL_fixed_height_strip χ T
  let K : Set ℂ := (fun p : ℝ × ℝ => (p.1:ℂ)+(p.2:ℂ)*I) ''
    (Set.Icc (1-δ) 2 ×ˢ Set.Icc (-T) T)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hmem (s : ℂ) : s ∈ K ↔ 1-δ ≤ s.re ∧ s.re ≤ 2 ∧ |s.im| ≤ T := by
    constructor
    · rintro ⟨⟨u,v⟩, ⟨hu, hv⟩, rfl⟩
      simpa [abs_le, and_assoc] using And.intro hu hv
    · rintro ⟨hs1, hs2, hs3⟩
      refine ⟨(s.re,s.im), ⟨⟨hs1,hs2⟩,abs_le.mp hs3⟩, ?_⟩
      exact Complex.re_add_im s
  have hc : ContinuousOn (primeLogDerivativeRegular χ) K := by
    intro s hs
    obtain ⟨hs1, hs2, hs3⟩ := (hmem s).mp hs
    exact (primeLogDerivativeRegular_analyticAt χ (hn s hs1 hs3)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨δ, max M 1, hδ, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro s hs1 hs2 hs3
  exact ⟨primeLogDerivativeRegular_analyticAt χ (hn s hs1 hs3),
    (hM s ((hmem s).mpr ⟨hs1,hs2,hs3⟩)).trans (le_max_left _ _)⟩

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_LogParameters

section File_OpenAIPrimeGaps_DirichletGrowth

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

open Filter Topology

open Complex Filter Topology

open Complex Filter Topology Set MeasureTheory Asymptotics

noncomputable def discrepancyTail (A : ℝ → ℂ) (u : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioi u, A t * (t:ℂ)^(-(s+1))

lemma discrepancyTail_integrable {A : ℝ → ℂ} {u D : ℝ} (hu : 0 < u) (hD : 0 ≤ D)
    (hA : Measurable A) (hbound : ∀ t, u < t → ‖A t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t => A t * (t:ℂ)^(-(s+1))) (Ioi u) := by
  have hp : (-(s+1)).re < -1 := by simp only [neg_re,add_re,one_re]; linarith
  have hi := (integrableOn_Ioi_norm_cpow_of_lt hp hu).const_mul D
  have hm := (integrableOn_Ioi_cpow_of_lt hp hu).aestronglyMeasurable
  refine hi.mono (hA.aestronglyMeasurable.restrict.mul hm) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hD (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg _)

lemma discrepancyTail_norm_le {A : ℝ → ℂ} {u D : ℝ} (hu : 0 < u) (_hD : 0 ≤ D)
    (_hA : Measurable A) (hbound : ∀ t, u < t → ‖A t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    ‖discrepancyTail A u s‖ ≤ D * u^(-s.re)/s.re := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) hu).const_mul D
  calc
    _ ≤ ∫ t in Ioi u, D*t^(-s.re-1) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (hu.trans ht)]
      simp only [neg_re,add_re,one_re,neg_add_rev]
      have he : -1 + -s.re = -s.re-1 := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_right (hbound t ht) (Real.rpow_nonneg (hu.trans ht).le _)
    _ = _ := by
      rw [integral_const_mul,integral_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) hu]
      ring_nf

lemma discrepancyTail_eq_mellin {A : ℝ → ℂ} {u : ℝ} (hu : 0 ≤ u) (s : ℂ) :
    discrepancyTail A u s = mellin ((Ioi u).indicator A) (-s) := by
  rw [mellin]
  simp_rw [←Set.indicator_smul]
  rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
  have he : Ioi u ∩ Ioi 0 = Ioi u := Set.inter_eq_left.mpr (fun t ht => hu.trans_lt ht)
  rw [he]
  unfold discrepancyTail
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  ring

lemma discrepancyTail_differentiableAt {A : ℝ → ℂ} {u D : ℝ} (hu : 0 < u) (hD : 0 ≤ D)
    (hA : Measurable A) (hbound : ∀ t, u < t → ‖A t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (discrepancyTail A u) s := by
  let B := (Ioi u).indicator A
  have hm : Measurable B := hA.indicator measurableSet_Ioi
  have hb : ∀ t, ‖B t‖ ≤ D := by
    intro t
    by_cases ht : u < t
    · simpa [B,ht] using hbound t ht
    · simpa [B,ht] using hD
  have hloc : LocallyIntegrableOn B (Ioi 0) :=
    ((locallyIntegrable_const D).mono hm.aestronglyMeasurable
      (.of_forall (fun t => (hb t).trans (le_abs_self D)))).locallyIntegrableOn _
  have htop : B =O[atTop] (fun t : ℝ => t^(-(0:ℝ))) := by
    refine isBigO_iff.mpr ⟨D,Eventually.of_forall ?_⟩
    intro t
    simpa using hb t
  have hbot : B =O[𝓝[>] 0] (fun t : ℝ => t^(-(-s.re-1))) := by
    refine isBigO_iff.mpr ⟨0,?_⟩
    filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds hu)] with t ht
    simp [B,not_lt.mpr ht.le]
  have hd := mellin_differentiableAt_of_isBigO_rpow hloc htop
    (by simpa using hs : (-s).re < 0) hbot (by simp : -s.re-1 < (-s).re)
  have he : discrepancyTail A u = fun z => mellin B (-z) := funext (discrepancyTail_eq_mellin hu.le)
  rw [he]
  exact hd.comp s differentiableAt_id.neg

open Finset

lemma periodic_sum_norm_le {f : ℕ → ℂ} {q : ℕ} (hq : 0 < q)
    (hp : ∀ n, f (q+n) = f n) (hz : ∑ n ∈ range q, f n = 0)
    (hb : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) : ‖∑ n ∈ range N, f n‖ ≤ q := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hN : N < q
    · calc
        _ ≤ ∑ n ∈ range N, ‖f n‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ range N, (1:ℝ) := sum_le_sum (fun n _ => hb n)
        _ = N := by simp
        _ ≤ q := by exact_mod_cast hN.le
    · have he : q+(N-q) = N := Nat.add_sub_of_le (not_lt.mp hN)
      rw [←he, sum_range_add, hz, zero_add]
      simp_rw [hp]
      exact ih _ (Nat.sub_lt (lt_of_lt_of_le hq (not_lt.mp hN)) hq)

lemma char_sum_range_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : ∑ n ∈ range q, χ (n : ZMod q) = 0 := by
  rw [←Fin.sum_univ_eq_sum_range]
  have he := (ZMod.finEquiv q).toEquiv.sum_comp χ
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    have hz := he.trans (MulChar.sum_eq_zero_of_ne_one hχ)
    change (∑ i : Fin (q+1), χ i) = 0 at hz
    calc
      _ = ∑ i : Fin (q+1), χ (i : Fin (q+1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        exact Fin.cast_val_eq_self i
      _ = 0 := hz

lemma char_sum_Icc_norm_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (N : ℕ) : ‖∑ n ∈ Icc 1 N, χ (n : ZMod q)‖ ≤ q+1 := by
  have hr := periodic_sum_norm_le (NeZero.pos q)
    (f := fun n => χ (n : ZMod q)) (by intro n; simp)
    (char_sum_range_zero hχ) (fun n => χ.norm_le_one _) (N+1)
  have he : ∑ n ∈ range (N+1), χ (n : ZMod q) =
      χ (0 : ZMod q) + ∑ n ∈ Icc 1 N, χ (n : ZMod q) := by
    rw [Nat.range_succ_eq_Icc_zero, ←Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le N)]
    simp
  rw [he] at hr
  calc
    _ = ‖(χ (0 : ZMod q) + ∑ n ∈ Icc 1 N, χ (n : ZMod q)) - χ 0‖ := by congr 1; ring
    _ ≤ ‖χ (0 : ZMod q) + ∑ n ∈ Icc 1 N, χ (n : ZMod q)‖ + ‖χ 0‖ := norm_sub_le _ _
    _ ≤ q+1 := add_le_add hr (χ.norm_le_one _)

noncomputable def seriesDiscrepancy (f : ℕ → ℂ) (c : ℂ) (t : ℝ) : ℂ :=
  (∑ n ∈ Icc 1 ⌊t⌋₊, f n) - c*t

lemma measurable_seriesDiscrepancy (f : ℕ → ℂ) (c : ℂ) :
    Measurable (seriesDiscrepancy f c) := by
  exact ((measurable_of_countable (fun N : ℕ => ∑ n ∈ Icc 1 N, f n)).comp
    Nat.measurable_floor).sub (measurable_const.mul Complex.continuous_ofReal.measurable)

noncomputable def regularSeries (f : ℕ → ℂ) (c : ℂ) (s : ℂ) : ℂ :=
  c+s*discrepancyTail (seriesDiscrepancy f c) 1 s

lemma regularSeries_differentiableAt {f : ℕ → ℂ} {c : ℂ} {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (regularSeries f c) s := by
  exact (differentiableAt_const c).add (differentiableAt_id.mul
    (discrepancyTail_differentiableAt zero_lt_one hD (measurable_seriesDiscrepancy f c) hb hs))

lemma regularSeries_eq_LSeries_sub {f : ℕ → ℂ} {c : ℂ} {D : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ 1) (hD : 0 ≤ D)
    (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D) {s : ℂ} (hs : 1 < s.re) :
    regularSeries f c s = LSeries f s - c/(s-1) := by
  have hO : (fun n => ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] (fun n => (n:ℝ)^(1:ℝ)) := by
    refine isBigO_iff.mpr ⟨1, .of_forall (fun n => ?_)⟩
    simp only [Real.rpow_one, one_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (sum_nonneg (fun _ _ => norm_nonneg _))]
    calc
      _ ≤ ∑ _k ∈ Icc 1 n, (1:ℝ) := sum_le_sum (fun n _ => hf n)
      _ ≤ |(n:ℝ)| := by simp
  rw [LSeries_eq_mul_integral' f zero_le_one hs hO]
  have hiA := discrepancyTail_integrable zero_lt_one hD (measurable_seriesDiscrepancy f c) hb
    (zero_lt_one.trans hs)
  have hi := integrableOn_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs : (-s).re < -1) zero_lt_one
  have he (t : ℝ) (ht : 1 < t) :
      (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t:ℂ)^(-(s+1)) =
      seriesDiscrepancy f c t * (t:ℂ)^(-(s+1)) + c*(t:ℂ)^(-s) := by
    have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans ht).ne'
    have ht1 : (t:ℂ)*(t:ℂ)^(-(s+1)) = (t:ℂ)^(-s) := by
      nth_rw 1 [←Complex.cpow_one (t:ℂ)]
      rw [←Complex.cpow_add _ _ ht0]
      congr 1
      ring
    dsimp [seriesDiscrepancy]
    rw [sub_mul, mul_assoc c, ht1]
    ring
  have hs0 : s-1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hv : ∫ t in Ioi (1:ℝ), (t:ℂ)^(-s) = 1/(s-1) := by
    rw [integral_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs : (-s).re < -1) zero_lt_one]
    simp only [ofReal_one, one_cpow]
    have he : -s+1 = -(s-1) := by ring
    rw [he, neg_div_neg_eq]
  rw [setIntegral_congr_fun measurableSet_Ioi he,
    integral_add hiA (hi.const_mul c), integral_const_mul, hv]
  dsimp [regularSeries,discrepancyTail]
  field_simp [hs0]
  ring

lemma sum_Icc_zero_eq {f : ℕ → ℂ} (hf : f 0 = 0) (N : ℕ) :
    ∑ k ∈ Icc 0 N, f k = ∑ k ∈ Icc 1 N, f k := by
  rw [←Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le N)]
  simp [hf]

lemma weighted_sum_abel {f : ℕ → ℂ} (hf : f 0 = 0) {N : ℕ} (hN : 1 ≤ N)
    {s : ℂ} (hs : 0 < s.re) :
    ∑ n ∈ Icc 1 N, f n * (n:ℂ)^(-s) =
      (∑ n ∈ Icc 1 N, f n)*(N:ℂ)^(-s) +
        s*∫ t in (1:ℝ)..N, (∑ n ∈ Icc 1 ⌊t⌋₊, f n)*(t:ℂ)^(-(s+1)) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  have hd (t:ℝ) (ht : t ∈ Set.Icc 1 (N:ℝ)) :
      HasDerivAt (fun t : ℝ => (t:ℂ)^(-s)) ((-s)*(t:ℂ)^(-(s+1))) t := by
    rw [show -(s+1) = -s-1 by ring]
    exact hasDerivAt_ofReal_cpow_const ((zero_lt_one.trans_le ht.1).ne') (neg_ne_zero.mpr hs0)
  have hcont : ContinuousOn (fun t : ℝ => (-s)*(t:ℂ)^(-(s+1))) (Set.Icc 1 (N:ℝ)) := by
    intro t ht
    exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const _ _
      (.inr (zero_lt_one.trans_le ht.1).ne'))).continuousWithinAt
  have hi : IntegrableOn (deriv (fun t:ℝ => (t:ℂ)^(-s))) (Set.Icc 1 (N:ℝ)) :=
    hcont.integrableOn_Icc.congr_fun (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have ha := sum_mul_eq_sub_sub_integral_mul' f hN (fun t ht => (hd t (by simpa using ht)).differentiableAt) (by simpa using hi)
  have he : (insert 1 (Finset.Ioc 1 N) : Finset ℕ) = Finset.Icc 1 N := by
    ext k
    simp only [Finset.mem_insert,Finset.mem_Ioc,Finset.mem_Icc]
    omega
  have hint : (∫ t in Set.Ioc (1:ℝ) (N:ℝ),
      deriv (fun t:ℝ => (t:ℂ)^(-s)) t * ∑ k ∈ Icc 0 ⌊t⌋₊, f k) =
      (-s)*∫ t in (1:ℝ)..N, (∑ k ∈ Icc 1 ⌊t⌋₊, f k)*(t:ℂ)^(-(s+1)) := by
    rw [intervalIntegral.integral_of_le hNR, ←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hd t ⟨ht.1.le,ht.2⟩).deriv,sum_Icc_zero_eq hf]
    ring
  simp only [Nat.cast_one, Complex.ofReal_natCast, Complex.ofReal_one] at ha
  rw [hint] at ha
  simp only [one_cpow,one_mul,sum_Icc_zero_eq hf,Finset.Icc_self,sum_singleton] at ha
  conv_lhs => rw [←he,sum_insert (by simp)]
  simp only [Nat.cast_one,one_cpow,mul_one]
  simp_rw [mul_comm (f _) ((_:ℂ)^(-s))]
  rw [ha]
  ring

lemma cpow_sub_eq_mul_intervalIntegral {N : ℝ} (hN : 1 ≤ N) (s : ℂ) :
    (N:ℂ)^(1-s)-1 = (1-s)*∫ t in (1:ℝ)..N, (t:ℂ)^(-s) := by
  by_cases hs : s = 1
  · subst s
    simp
  · have hn : (0:ℝ) ∉ Set.uIcc 1 N := by rw [Set.uIcc_of_le hN]; simp
    rw [integral_cpow (.inr ⟨by simpa using hs,hn⟩)]
    simp only [Complex.ofReal_one,one_cpow]
    have he : -s+1 = 1-s := by ring
    rw [he]
    field_simp

lemma regularSeries_cutoff {f : ℕ → ℂ} {c : ℂ} {D : ℝ} (hf : f 0 = 0)
    (hD : 0 ≤ D) (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D)
    {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    regularSeries f c s = (∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) -
      seriesDiscrepancy f c N * (N:ℂ)^(-s) +
      s*discrepancyTail (seriesDiscrepancy f c) N s -
      c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N:ℂ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN).ne'
  have hi := discrepancyTail_integrable zero_lt_one hD (measurable_seriesDiscrepancy f c) hb hs
  have htail := intervalIntegral.integral_Ioi_sub_Ioi hi hNR
  have hp : ∀ t ∈ Set.Icc (1:ℝ) (N:ℝ),
      (t:ℂ)*(t:ℂ)^(-(s+1)) = (t:ℂ)^(-s) := by
    intro t ht
    have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le ht.1).ne'
    nth_rw 1 [←Complex.cpow_one (t:ℂ)]
    rw [←Complex.cpow_add _ _ ht0]
    congr 1
    ring
  have hip : IntervalIntegrable (fun t:ℝ => (t:ℂ)^(-s)) volume 1 N :=
    intervalIntegral.intervalIntegrable_cpow (.inr (by rw [Set.uIcc_of_le hNR]; simp))
  have hiA : IntervalIntegrable (fun t:ℝ => seriesDiscrepancy f c t*(t:ℂ)^(-(s+1))) volume 1 N :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hNR).mpr (hi.mono_set Set.Ioc_subset_Ioi_self)
  have hint : (∫ t in (1:ℝ)..N, (∑ n ∈ Icc 1 ⌊t⌋₊, f n)*(t:ℂ)^(-(s+1))) =
      (∫ t in (1:ℝ)..N, seriesDiscrepancy f c t*(t:ℂ)^(-(s+1))) +
        c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s) := by
    rw [←intervalIntegral.integral_const_mul, ←intervalIntegral.integral_add hiA (hip.const_mul c)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hNR] at ht
    dsimp [seriesDiscrepancy]
    rw [sub_mul,mul_assoc c,hp t ht]
    ring
  have hab := weighted_sum_abel hf hN hs
  rw [hint, ←htail] at hab
  have hpow : (N:ℂ)*(N:ℂ)^(-s) = (N:ℂ)^(1-s) := by
    nth_rw 1 [←Complex.cpow_one (N:ℂ)]
    rw [←Complex.cpow_add _ _ hn0]
    congr 1
  have hc := cpow_sub_eq_mul_intervalIntegral hNR s
  simp only [Complex.ofReal_natCast] at hc
  dsimp [regularSeries,discrepancyTail]
  rw [hab]
  simp only [seriesDiscrepancy,Nat.floor_natCast,Complex.ofReal_natCast]
  rw [sub_mul,mul_assoc c,hpow,sub_eq_iff_eq_add.mp hc]
  ring

lemma sum_cpow_norm_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {ε : ℝ} (hε : 0 < ε)
    {s : ℂ} (hs : 1-ε ≤ s.re) {N : ℕ} (_hN : 1 ≤ N) :
    ‖∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)‖ ≤
      (∑' n : ℕ, (n:ℝ)^(-1-ε)) * (N:ℝ)^(2*ε) := by
  have hsumm : Summable (fun n : ℕ => (n:ℝ)^(-1-ε)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ‖f n*(n:ℂ)^(-s)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 N, (n:ℝ)^(-1-ε)*(N:ℝ)^(2*ε) := by
      apply sum_le_sum
      intro n hn
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
      have hnN : (n:ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
      have hn0 := zero_lt_one.trans_le hn1
      rw [norm_mul]
      have hn0C : (n:ℂ) = ((n:ℝ):ℂ) := by simp
      rw [hn0C,Complex.norm_cpow_eq_rpow_re_of_pos hn0,Complex.neg_re]
      calc
        _ ≤ (n:ℝ)^(-s.re) := by
          simpa using mul_le_mul_of_nonneg_right (hf n) (Real.rpow_nonneg hn0.le (-s.re))
        _ ≤ (n:ℝ)^(-1+ε) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        _ = (n:ℝ)^(-1-ε)*(n:ℝ)^(2*ε) := by rw [←Real.rpow_add hn0]; congr 1; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn0.le hnN (by positivity))
          (Real.rpow_nonneg hn0.le _)
    _ = (∑ n ∈ Icc 1 N, (n:ℝ)^(-1-ε))*(N:ℝ)^(2*ε) := by rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hsumm.sum_le_tsum _ (fun n _ => Real.rpow_nonneg n.cast_nonneg _))
      (Real.rpow_nonneg N.cast_nonneg _)

lemma norm_intervalIntegral_cpow_le {ε N : ℝ} (hε : 0 < ε) (hN : 1 ≤ N)
    {s : ℂ} (hs : 1-ε ≤ s.re) :
    ‖∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ ≤ N^ε/ε := by
  have hn : (0:ℝ) ∉ Set.uIcc 1 N := by rw [Set.uIcc_of_le hN]; simp
  calc
    _ ≤ ∫ t in (1:ℝ)..N, t^(-1+ε) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hN
        (.of_forall (fun t ht => ?_)) (intervalIntegral.intervalIntegrable_rpow (.inr hn))
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht.1),Complex.neg_re]
      exact Real.rpow_le_rpow_of_exponent_le ht.1.le (by linarith)
    _ = (N^ε-1)/ε := by
      rw [integral_rpow (.inl (by linarith : -1 < -1+ε))]
      have he : -1+ε+1 = ε := by ring
      simp [he]
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hε.le

lemma regularSeries_norm_cutoff {f : ℕ → ℂ} {c : ℂ} {D ε : ℝ}
    (hf0 : f 0 = 0) (hf : ∀ n, ‖f n‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hD : 0 ≤ D)
    (hb : ∀ t, 1 ≤ t → ‖seriesDiscrepancy f c t‖ ≤ D)
    (hε : 0 < ε) (hε1 : ε ≤ 1/2) {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hs : 1-ε ≤ s.re) (hNs : D*(1+‖s‖) ≤ N) :
    ‖regularSeries f c s‖ ≤ ((∑' n : ℕ, (n:ℝ)^(-1-ε))+2+1/ε)*(N:ℝ)^(2*ε) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNP := zero_lt_one.trans_le hNR
  have hs0 : 0 < s.re := by linarith
  have hhalf : 1/2 ≤ s.re := by linarith
  have htail := discrepancyTail_norm_le hNP hD (measurable_seriesDiscrepancy f c)
    (fun t ht => hb t (hNR.trans ht.le)) hs0
  have hboundary : ‖seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ ≤ D*(N:ℝ)^(-s.re) := by
    rw [norm_mul, ←Complex.ofReal_natCast N, Complex.norm_cpow_eq_rpow_re_of_pos hNP,Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (hb _ hNR) (Real.rpow_nonneg hNP.le _)
  have hsmall : ‖seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ +
      ‖s*discrepancyTail (seriesDiscrepancy f c) N s‖ ≤ 2*(N:ℝ)^ε := by
    have ht : D*(N:ℝ)^(-s.re)/s.re ≤ 2*D*(N:ℝ)^(-s.re) := by
      apply (div_le_iff₀ hs0).mpr
      have hn := Real.rpow_nonneg hNP.le (-s.re)
      nlinarith [mul_nonneg hD hn,mul_nonneg (mul_nonneg hD hn) (sub_nonneg.mpr hhalf)]
    have he : (N:ℝ)*(N:ℝ)^(-s.re) ≤ (N:ℝ)^ε := by
      nth_rw 1 [←Real.rpow_one (N:ℝ)]
      rw [←Real.rpow_add hNP]
      apply Real.rpow_le_rpow_of_exponent_le hNR
      linarith
    calc
      _ ≤ D*(N:ℝ)^(-s.re) + ‖s‖*(2*D*(N:ℝ)^(-s.re)) := by
        nth_rw 2 [norm_mul]
        exact add_le_add hboundary (mul_le_mul_of_nonneg_left (htail.trans ht) (norm_nonneg s))
      _ ≤ 2*(N:ℝ)*(N:ℝ)^(-s.re) := by
        have hcoeff : D+2*‖s‖*D ≤ 2*(N:ℝ) := by nlinarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hcoeff) (Real.rpow_nonneg hNP.le (-s.re))]
      _ ≤ _ := by nlinarith [he]
  have hi : ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ ≤ (N:ℝ)^ε/ε := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans (by
      simpa using norm_intervalIntegral_cpow_le hε hNR hs)
  have hp : (N:ℝ)^ε ≤ (N:ℝ)^(2*ε) := Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
  rw [regularSeries_cutoff hf0 hD (fun t ht => hb t ht.le) hN hs0]
  calc
    _ ≤ ‖∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)‖ +
        (‖seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ +
        ‖s*discrepancyTail (seriesDiscrepancy f c) N s‖) +
        ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ := by
      calc
        _ ≤ ‖(∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) - seriesDiscrepancy f c N * (N:ℂ)^(-s) +
             s*discrepancyTail (seriesDiscrepancy f c) N s‖ +
             ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ := norm_sub_le _ _
        _ ≤ (‖(∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) - seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ +
             ‖s*discrepancyTail (seriesDiscrepancy f c) N s‖) +
             ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ := add_le_add (norm_add_le _ _) le_rfl
        _ ≤ _ := by
          have htri := norm_sub_le (∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) (seriesDiscrepancy f c N * (N:ℂ)^(-s))
          linarith
    _ ≤ ((∑' n : ℕ, (n:ℝ)^(-1-ε)))*(N:ℝ)^(2*ε) +
      2*(N:ℝ)^ε+(N:ℝ)^ε/ε := add_le_add (add_le_add (sum_cpow_norm_le hf hε hs hN) hsmall) hi
    _ ≤ ((∑' n : ℕ, (n:ℝ)^(-1-ε)))*(N:ℝ)^(2*ε) +
      2*(N:ℝ)^(2*ε)+(N:ℝ)^(2*ε)/ε := by
        linarith [div_le_div_of_nonneg_right hp hε.le]
    _ = _ := by ring

lemma regularSeries_norm_small_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℕ → ℂ) (c : ℂ) (D : ℝ),
      f 0 = 0 → (∀ n, ‖f n‖ ≤ 1) → ‖c‖ ≤ 1 → 0 ≤ D →
      (∀ t, 1 ≤ t → ‖seriesDiscrepancy f c t‖ ≤ D) →
      ∀ s : ℂ, 1-ε ≤ s.re →
      ‖regularSeries f c s‖ ≤ K*((D+1)*(‖s‖+2))^(2*ε) := by
  let K₀ := (∑' n : ℕ, (n:ℝ)^(-1-ε))+2+1/ε
  have hK₀ : 0 < K₀ := by
    have ht : 0 ≤ ∑' n : ℕ, (n:ℝ)^(-1-ε) := tsum_nonneg (fun n => Real.rpow_nonneg n.cast_nonneg _)
    dsimp [K₀]
    positivity
  refine ⟨K₀*2^(2*ε), by positivity, ?_⟩
  intro f c D hf0 hf hc hD hb s hs
  let B := (D+1)*(‖s‖+2)
  have hB : 1 ≤ B := by dsimp [B]; nlinarith [norm_nonneg s]
  let N := ⌈B⌉₊
  have hBN : B ≤ (N:ℝ) := Nat.le_ceil B
  have hN : 1 ≤ N := by exact_mod_cast (hB.trans hBN)
  have hN2 : (N:ℝ) ≤ 2*B := by
    have := Nat.ceil_lt_add_one (zero_lt_one.trans_le hB).le
    change (N:ℝ) < B+1 at this
    linarith
  have hcut := regularSeries_norm_cutoff hf0 hf hc hD hb hε hε1 hN hs
    (show D*(1+‖s‖) ≤ (N:ℝ) from (by dsimp [B] at hBN; nlinarith [norm_nonneg s]))
  calc
    _ ≤ K₀*(N:ℝ)^(2*ε) := hcut
    _ ≤ K₀*(2*B)^(2*ε) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow N.cast_nonneg hN2 (by positivity)) hK₀.le
    _ = _ := by rw [Real.mul_rpow (by norm_num) (by linarith : 0 ≤ B)]; ring

def positiveCoefficients (f : ℕ → ℂ) (n : ℕ) : ℂ := if n = 0 then 0 else f n

lemma positiveCoefficients_zero (f : ℕ → ℂ) : positiveCoefficients f 0 = 0 := by simp [positiveCoefficients]

lemma positiveCoefficients_norm_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (n : ℕ) :
    ‖positiveCoefficients f n‖ ≤ 1 := by
  by_cases hn : n=0 <;> simp [positiveCoefficients,hn,hf]

lemma sum_positiveCoefficients (f : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, positiveCoefficients f n = ∑ n ∈ Icc 1 N, f n := by
  apply sum_congr rfl
  intro n hn
  simp [positiveCoefficients,show n ≠ 0 from Nat.ne_of_gt (mem_Icc.mp hn).1]

lemma LSeries_positiveCoefficients (f : ℕ → ℂ) (s : ℂ) :
    LSeries (positiveCoefficients f) s = LSeries f s := by
  apply LSeries_congr
  intro n hn
  simp [positiveCoefficients,hn]

lemma discrepancy_character_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (t : ℝ) :
    ‖seriesDiscrepancy (positiveCoefficients (fun n => χ (n : ZMod q))) 0 t‖ ≤ q+1 := by
  simpa [seriesDiscrepancy,sum_positiveCoefficients] using char_sum_Icc_norm_le hχ ⌊t⌋₊

lemma discrepancy_constant_bound {t : ℝ} (ht : 1 ≤ t) :
    ‖seriesDiscrepancy (positiveCoefficients (fun _ => 1)) 1 t‖ ≤ 1 := by
  simp only [seriesDiscrepancy,sum_positiveCoefficients,Finset.sum_const,nsmul_eq_mul,
    mul_one,Nat.card_Icc,Nat.add_sub_cancel,one_mul]
  rw [←Complex.ofReal_natCast,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have ht0 := (show (0:ℝ) ≤ t by linarith)
  rw [abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le ht0))]
  have := Nat.lt_floor_add_one t
  linarith

lemma regularSeries_character_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) 0 s = χ.LFunction s := by
  let f := positiveCoefficients (fun n => χ (n : ZMod q))
  have hfrac : AnalyticOnNhd ℂ (regularSeries f 0) {s : ℂ | 0 < s.re} := by
    apply DifferentiableOn.analyticOnNhd ?_ (continuous_re.isOpen_preimage _ isOpen_Ioi)
    intro s hs
    exact (regularSeries_differentiableAt (by positivity : (0:ℝ) ≤ q+1)
      (fun t _ => discrepancy_character_bound hχ t) hs).differentiableWithinAt
  have hL : AnalyticOnNhd ℂ χ.LFunction {s : ℂ | 0 < s.re} :=
    fun s _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt s
  have he : regularSeries f 0 =ᶠ[𝓝 (2:ℂ)] χ.LFunction := by
    filter_upwards [(continuous_re.tendsto (2:ℂ)).eventually (lt_mem_nhds (by norm_num : (1:ℝ) < (2:ℂ).re))] with z hz
    rw [regularSeries_eq_LSeries_sub (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
      (by positivity : (0:ℝ) ≤ q+1) (fun t _ => discrepancy_character_bound hχ t) hz]
    simp only [zero_div,sub_zero]
    rw [LSeries_positiveCoefficients,DirichletCharacter.LFunction_eq_LSeries χ hz]
  exact hfrac.eqOn_of_preconnected_of_eventuallyEq hL (convex_halfSpace_re_gt 0).isPreconnected
    (show (2:ℂ) ∈ {s:ℂ | 0<s.re} by norm_num) he hs

lemma LFunction_norm_small_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, 1-ε ≤ s.re →
      ‖χ.LFunction s‖ ≤ K*((q+2)*(‖s‖+2))^(2*ε) := by
  obtain ⟨K,hK,h⟩ := regularSeries_norm_small_power hε hε1
  refine ⟨K,hK,fun q _ χ hχ s hs => ?_⟩
  have he := h _ 0 (q+1) (positiveCoefficients_zero _) (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
    (by simp) (by positivity) (fun t _ => discrepancy_character_bound hχ t) s hs
  rw [regularSeries_character_eq hχ (by linarith)] at he
  convert he using 1
  congr 3
  ring

lemma regularSeries_deriv_norm_small_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℕ → ℂ) (c : ℂ) (D : ℝ),
      f 0 = 0 → (∀ n, ‖f n‖ ≤ 1) → ‖c‖ ≤ 1 → 0 ≤ D →
      (∀ t, 1 ≤ t → ‖seriesDiscrepancy f c t‖ ≤ D) →
      ∀ s : ℂ, 1-ε/2 ≤ s.re →
      ‖deriv (regularSeries f c) s‖ ≤ K*((D+1)*(‖s‖+2))^(2*ε) := by
  obtain ⟨K,hK,h⟩ := regularSeries_norm_small_power hε hε1
  refine ⟨K*2^(2*ε)/(ε/2),by positivity,?_⟩
  intro f c D hf0 hf hc hD hb s hs
  have hε2 : 0 < ε/2 := by positivity
  have hre (z:ℂ) (hz : dist z s ≤ ε/2) : 1-ε ≤ z.re := by
    have hd := Complex.re_le_norm (s-z)
    rw [Complex.sub_re,←dist_eq_norm,dist_comm] at hd
    linarith
  have hd : DiffContOnCl ℂ (regularSeries f c) (Metric.ball s (ε/2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hε2.ne']
    intro z hz
    exact (regularSeries_differentiableAt hD (fun t ht => hb t ht.le) (by
      have := hre z (Metric.mem_closedBall.mp hz)
      linarith)).differentiableWithinAt
  have hbnd (z:ℂ) (hz : z ∈ Metric.sphere s (ε/2)) :
      ‖regularSeries f c z‖ ≤ K*2^(2*ε)*((D+1)*(‖s‖+2))^(2*ε) := by
    have hdist := Metric.mem_sphere.mp hz
    have hzR := hre z hdist.le
    have hnorm : ‖z‖+2 ≤ 2*(‖s‖+2) := by
      have : ‖z‖ ≤ dist z s + ‖s‖ := by simpa [dist_eq_norm] using norm_add_le (z-s) s
      rw [hdist] at this
      nlinarith [norm_nonneg s]
    calc
      _ ≤ K*((D+1)*(‖z‖+2))^(2*ε) := h f c D hf0 hf hc hD hb z hzR
      _ ≤ K*(2*((D+1)*(‖s‖+2)))^(2*ε) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)) hK.le
      _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity)]; ring
  have hder := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hε2 hd hbnd
  convert hder using 1
  ring

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_DirichletGrowth

section File_OpenAIPrimeGaps_TaylorBounds

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

open Filter Topology

open Complex Filter Topology

open Complex Filter Topology Set MeasureTheory Asymptotics

open Finset

open Complex Filter Topology Finset

lemma power_series_tail_bound {a : ℕ → ℝ} {M r z : ℝ} (_hM : 0 ≤ M)
    (hr : 0 < r) (hz : 0 ≤ z) (hzr : z < r)
    (hb : ∀ n, |a n| ≤ M/r^n) (N : ℕ) :
    |∑' n : ℕ, a (n+N)*z^(n+N)| ≤ M*(z/r)^N/(1-z/r) := by
  have hρ : 0 ≤ z/r := div_nonneg hz hr.le
  have hρ1 : z/r < 1 := (div_lt_one hr).mpr hzr
  have hg := (summable_geometric_of_lt_one hρ hρ1).mul_left (M*(z/r)^N)
  have hbound (n : ℕ) : ‖a (n+N)*z^(n+N)‖ ≤ (M*(z/r)^N)*(z/r)^n := by
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg hz _)]
    calc
      _ ≤ (M/r^(n+N))*z^(n+N) := mul_le_mul_of_nonneg_right (hb _) (pow_nonneg hz _)
      _ = M*(z/r)^(n+N) := by rw [div_pow]; ring
      _ = _ := by rw [pow_add]; ring
  have hn := hg.of_nonneg_of_le (fun n => norm_nonneg _) hbound
  calc
    _ = ‖∑' n : ℕ, a (n+N)*z^(n+N)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : ℕ, ‖a (n+N)*z^(n+N)‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n : ℕ, (M*(z/r)^N)*(z/r)^n := hn.tsum_le_tsum hbound hg
    _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one hρ hρ1]; rfl

lemma residue_lower_bound_of_taylor {a : ℕ → ℝ} {R M r z : ℝ} {N : ℕ}
    (hM : 0 ≤ M) (hr : 0 < r) (hz : 1 < z) (hzr : z < r)
    (hb : ∀ n, |a n| ≤ M/r^n) (ha0 : 1-R ≤ a 0)
    (ha : ∀ n, -R ≤ a n) (hN : 1 ≤ N)
    (hvalue : (∑' n : ℕ, a n*z^n) ≤ R/(z-1))
    (htail : M*(z/r)^N/(1-z/r) ≤ 1/2) :
    (z-1)/2 ≤ R*z^N := by
  have heach : ∀ n, (if n=0 then 1 else (0:ℝ)) - R*z^n ≤ a n*z^n := by
    intro n
    by_cases hn : n=0
    · simpa [hn] using ha0
    · simp only [hn,↓reduceIte,zero_sub]
      nlinarith [mul_le_mul_of_nonneg_right (ha n) (pow_nonneg (zero_lt_one.trans hz).le n)]
  have hsum := Finset.sum_le_sum (s := range N) (fun n _ => heach n)
  have hzero : (∑ n ∈ range N, if n=0 then 1 else (0:ℝ)) = 1 := by
    simp [show 0 < N by omega]
  rw [sum_sub_distrib,hzero,←mul_sum] at hsum
  have htail' := power_series_tail_bound hM hr (zero_lt_one.trans hz).le hzr hb N
  have ht : -(1/2:ℝ) ≤ ∑' n : ℕ, a (n+N)*z^(n+N) := by
    have := (abs_le.mp (htail'.trans htail)).1
    linarith
  have hs : Summable (fun n : ℕ => a n*z^n) := by
    have hρ : 0 ≤ z/r := by positivity
    have hρ1 : z/r < 1 := (div_lt_one hr).mpr hzr
    apply ((summable_geometric_of_lt_one hρ hρ1).mul_left M).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg (zero_lt_one.trans hz).le _)]
    calc
      _ ≤ (M/r^n)*z^n := mul_le_mul_of_nonneg_right (hb _) (pow_nonneg (zero_lt_one.trans hz).le _)
      _ = M*(z/r)^n := by rw [div_mul_eq_mul_div,div_pow]; ring
  have hdecomp := hs.sum_add_tsum_nat_add N
  have hm : 1/2 ≤ R/(z-1)+R*(∑ n ∈ range N, z^n) := by linarith
  have hgeom := geom_sum_mul z N
  have hv := (le_div_iff₀ (sub_pos.mpr hz)).mp
    (show (1/2:ℝ) ≤ (R+R*(∑ n ∈ range N, z^n)*(z-1))/(z-1) from by
      rw [add_div,mul_div_cancel_right₀ _ (sub_pos.mpr hz).ne']
      exact hm)
  have hid : R+R*(∑ n ∈ range N, z^n)*(z-1) = R*z^N := by
    rw [mul_assoc R, hgeom]
    ring
  rw [hid] at hv
  linarith

noncomputable def signedTaylorCoeff (H : ℂ → ℂ) (n : ℕ) : ℝ :=
  (((-1:ℂ)^n)*(n.factorial:ℂ)⁻¹*iteratedDeriv n H 2).re

lemma signedTaylorCoeff_hasSum {H : ℂ → ℂ} {r z : ℝ}
    (hf : DifferentiableOn ℂ H (Metric.ball 2 r)) (hz : |z| < r) :
    HasSum (fun n => signedTaylorCoeff H n*z^n) (H ((2-z:ℝ):ℂ)).re := by
  have hmem : ((2-z:ℝ):ℂ) ∈ Metric.ball (2:ℂ) r := by
    rw [Metric.mem_ball,dist_eq_norm]
    have he : ((2-z:ℝ):ℂ)-(2:ℂ) = -(z:ℂ) := by push_cast; ring
    simpa [he,Complex.norm_real,Real.norm_eq_abs] using hz
  have hs := (Complex.hasSum_taylorSeries_on_ball hf hmem).map Complex.reCLM Complex.continuous_re
  change HasSum (fun n => ((n.factorial:ℂ)⁻¹ *
    ((((2-z:ℝ):ℂ)-2)^n * iteratedDeriv n H 2)).re) (H ((2-z:ℝ):ℂ)).re at hs
  convert hs using 1
  funext n
  dsimp [signedTaylorCoeff]
  have he : ((2-z:ℝ):ℂ)-(2:ℂ) = -(z:ℂ) := by push_cast; ring
  rw [he, show (-(z:ℂ))^n = (-1:ℂ)^n * (z:ℂ)^n by rw [←mul_pow]; congr 1; ring]
  have hmul : (n.factorial:ℂ)⁻¹*((-1:ℂ)^n*(z:ℂ)^n*iteratedDeriv n H 2) =
      ((-1:ℂ)^n*(n.factorial:ℂ)⁻¹*iteratedDeriv n H 2)*(z:ℂ)^n := by ring
  rw [hmul]
  simp only [←Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero]

lemma signedTaylorCoeff_norm_bound {H : ℂ → ℂ} {r M : ℝ} (hr : 0 < r)
    (hf : DiffContOnCl ℂ H (Metric.ball 2 r))
    (hb : ∀ s ∈ Metric.sphere 2 r, ‖H s‖ ≤ M) (n : ℕ) :
    |signedTaylorCoeff H n| ≤ M/r^n := by
  have hder := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hf hb
  have hfact : (n.factorial:ℝ) ≠ 0 := by positivity
  calc
    _ ≤ ‖(-1:ℂ)^n*(n.factorial:ℂ)⁻¹*iteratedDeriv n H 2‖ := Complex.abs_re_le_norm _
    _ = (n.factorial:ℝ)⁻¹*‖iteratedDeriv n H 2‖ := by simp [norm_pow]
    _ ≤ (n.factorial:ℝ)⁻¹*((n.factorial:ℝ)*M/r^n) := by gcongr
    _ = _ := by field_simp

lemma signedTaylorCoeff_residue {H : ℂ → ℂ} {R M r z : ℝ} {N : ℕ}
    (hM : 0 ≤ M) (hr : 0 < r) (hz : 1 < z) (hzr : z < r)
    (hf : DiffContOnCl ℂ H (Metric.ball 2 r))
    (hb : ∀ s ∈ Metric.sphere 2 r, ‖H s‖ ≤ M)
    (ha0 : 1-R ≤ (H 2).re) (ha : ∀ n, -R ≤ signedTaylorCoeff H n)
    (hN : 1 ≤ N) (hvalue : (H ((2-z:ℝ):ℂ)).re ≤ R/(z-1))
    (htail : M*(z/r)^N/(1-z/r) ≤ 1/2) :
    (z-1)/2 ≤ R*z^N := by
  apply residue_lower_bound_of_taylor hM hr hz hzr (signedTaylorCoeff_norm_bound hr hf hb)
    (by simpa [signedTaylorCoeff] using ha0) ha hN ?_ htail
  rw [(signedTaylorCoeff_hasSum hf.differentiableOn (by rwa [abs_of_pos (zero_lt_one.trans hz)])).tsum_eq]
  exact hvalue

lemma signedTaylorCoeff_pole (R : ℝ) (n : ℕ) :
    signedTaylorCoeff (fun s : ℂ => (R:ℂ)/(s-1)) n = R := by
  unfold signedTaylorCoeff
  simp only [div_eq_mul_inv,iteratedDeriv_const_mul_field]
  have hi : iteratedDeriv n (fun s : ℂ => (s-1)⁻¹) 2 = (-1:ℂ)^n*n.factorial := by
    rw [iteratedDeriv_eq_iterate]
    simpa only [one_mul,one_pow, show (2:ℂ)-1=1 by norm_num, one_zpow,mul_one] using
      congrFun (iter_deriv_inv_linear_sub n (1:ℂ) 1) 2
  rw [hi]
  have hf : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hp : (-1:ℂ)^n*(-1:ℂ)^n = 1 := by rw [←mul_pow]; simp
  have he : (-1:ℂ)^n*(n.factorial:ℂ)⁻¹*((R:ℂ)*((-1:ℂ)^n*n.factorial)) = R := by
    calc
      _ = ((-1:ℂ)^n*(-1:ℂ)^n)*(R:ℂ)*((n.factorial:ℂ)⁻¹*n.factorial) := by ring
      _ = _ := by rw [hp,inv_mul_cancel₀ hf]; ring
  rw [he,Complex.ofReal_re]

lemma signedTaylorCoeff_sub {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 2)
    (hG : AnalyticAt ℂ G 2) (n : ℕ) :
    signedTaylorCoeff (fun s => F s-G s) n = signedTaylorCoeff F n-signedTaylorCoeff G n := by
  unfold signedTaylorCoeff
  have hd := iteratedDeriv_sub (n:=n) hF.contDiffAt hG.contDiffAt
  change iteratedDeriv n (fun s => F s-G s) 2 = _ at hd
  rw [hd,mul_sub,Complex.sub_re]

open scoped ComplexOrder in
lemma signedTaylorCoeff_LSeries_nonneg {a : ℕ → ℂ} (ha : ∀ n, 0 ≤ a n)
    (hc : LSeries.abscissaOfAbsConv a < (2:ℝ)) (n : ℕ) :
    0 ≤ signedTaylorCoeff (LSeries a) n := by
  have h := LSeries.iteratedDeriv_alternating ha hc n
  have hf : (0:ℝ) ≤ (n.factorial:ℝ)⁻¹ := by positivity
  have hr := (Complex.nonneg_iff.mp h).1
  unfold signedTaylorCoeff
  have he : (-1:ℂ)^n*(n.factorial:ℂ)⁻¹*iteratedDeriv n (LSeries a) 2 =
      (n.factorial:ℂ)⁻¹*((-1:ℂ)^n*iteratedDeriv n (LSeries a) 2) := by ring
  rw [he]
  simpa using mul_nonneg hf hr

open scoped ComplexOrder in
lemma LSeries_two_re_ge_one {a : ℕ → ℂ} (ha : ∀ n, 0 ≤ a n)
    (ha1 : 1 ≤ a 1) (hc : LSeries.abscissaOfAbsConv a < (2:ℝ)) :
    1 ≤ (LSeries a 2).re := by
  have hs : LSeriesSummable a 2 := LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hc)
  have hl := hs.le_tsum 1 (fun n _ => LSeries.term_nonneg (ha n) 2)
  have hterm : LSeries.term a 2 1 = a 1 := by simp
  rw [hterm] at hl
  exact (Complex.le_def.mp (ha1.trans hl)).1

open scoped ComplexOrder in
lemma signedTaylorCoeff_regular_nonneg {H : ℂ → ℂ} {a : ℕ → ℂ} {R : ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha1 : 1 ≤ a 1)
    (hc : LSeries.abscissaOfAbsConv a < (2:ℝ))
    (he : H =ᶠ[𝓝 (2:ℂ)] fun s => LSeries a s-(R:ℂ)/(s-1)) :
    1-R ≤ (H 2).re ∧ ∀ n, -R ≤ signedTaylorCoeff H n := by
  have hL : AnalyticAt ℂ (LSeries a) 2 := LSeries_analyticOnNhd a 2 (by simpa using hc)
  have hP : AnalyticAt ℂ (fun s : ℂ => (R:ℂ)/(s-1)) 2 :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (by norm_num)
  constructor
  · rw [he.self_of_nhds]
    have h := LSeries_two_re_ge_one ha ha1 hc
    simp only [show (2:ℂ)-1=1 by norm_num,div_one,Complex.sub_re,Complex.ofReal_re]
    linarith
  · intro n
    unfold signedTaylorCoeff
    rw [he.iteratedDeriv_eq]
    change -R ≤ signedTaylorCoeff (fun s => LSeries a s-(R:ℂ)/(s-1)) n
    rw [signedTaylorCoeff_sub hL hP,signedTaylorCoeff_pole]
    linarith [signedTaylorCoeff_LSeries_nonneg ha hc n]

lemma residue_polynomial_lower {a : ℕ → ℝ} {R A Q z ε : ℝ}
    (hA : 0 ≤ A) (hQ : 2 ≤ Q) (hQA : 12*A ≤ Q)
    (hz : 1 < z) (hz1 : z ≤ 5/4) (hzε : 60*(z-1) ≤ ε)
    (hb : ∀ n, |a n| ≤ (A*Q^4)/(3/2)^n)
    (ha0 : 1-R ≤ a 0) (ha : ∀ n, -R ≤ a n)
    (hv : (∑' n : ℕ, a n*z^n) ≤ R/(z-1)) :
    ((z-1)/(2*z))*Q^(-ε) ≤ R := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hz0 : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos hz
  let N : ℕ := ⌈60*Real.log Q⌉₊
  have hNlo : 60*Real.log Q ≤ (N:ℝ) := Nat.le_ceil _
  have hNhi : (N:ℝ) < 60*Real.log Q+1 := Nat.ceil_lt_add_one (by positivity)
  have hN : 1 ≤ N := by
    have : 0 < (N:ℝ) := lt_of_lt_of_le (by positivity) hNlo
    exact_mod_cast (show 1 ≤ N from Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast this.ne'))
  have hρ : 0 ≤ z/(3/2) := by positivity
  have hρ1 : z/(3/2) ≤ 5/6 := by linarith
  have hlogρ : Real.log (5/6:ℝ) ≤ -(1/6:ℝ) := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 5/6)
    linarith
  have hdecay : (z/(3/2))^N ≤ Q^(-10:ℝ) := by
    calc
      _ ≤ (5/6:ℝ)^N := pow_le_pow_left₀ hρ hρ1 N
      _ = Real.exp (Real.log (5/6:ℝ)*(N:ℝ)) := by
        rw [←Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 5/6)]
      _ ≤ Real.exp (Real.log Q*(-10)) := by
        apply Real.exp_le_exp.mpr
        have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
        nlinarith [mul_le_mul_of_nonneg_right hlogρ hN0]
      _ = _ := (Real.rpow_def_of_pos hQ0 _).symm
  have htail : (A*Q^4)*(z/(3/2))^N/(1-z/(3/2)) ≤ 1/2 := by
    have hden : 0 < 1-z/(3/2) := by linarith
    have hpow : Q^4*Q^(-10:ℝ) ≤ Q⁻¹ := by
      calc
        _ = Q^(-6:ℝ) := by
          rw [←Real.rpow_natCast,←Real.rpow_add hQ0]
          norm_num
        _ ≤ Q^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
        _ = Q⁻¹ := Real.rpow_neg_one Q
    have hp : (A*Q^4)*(z/(3/2))^N ≤ A/Q := by
      calc
        _ ≤ (A*Q^4)*Q^(-10:ℝ) := mul_le_mul_of_nonneg_left hdecay (by positivity)
        _ ≤ A*Q⁻¹ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hpow hA
        _ = _ := by rw [div_eq_mul_inv]
    have hAQ : A/Q ≤ 1/12 := (div_le_iff₀ hQ0).mpr (by linarith)
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hres := residue_lower_bound_of_taylor (by positivity : (0:ℝ) ≤ A*Q^4)
    (by norm_num : (0:ℝ) < 3/2) hz (by linarith : z < 3/2) hb ha0 ha hN hv htail
  have hzpow : z^N ≤ z*Q^ε := by
    have hlogz' : 60*Real.log z ≤ ε := by
      have := Real.log_le_sub_one_of_pos hz0
      linarith
    calc
      _ = Real.exp (Real.log z*(N:ℝ)) := by rw [←Real.rpow_natCast,Real.rpow_def_of_pos hz0]
      _ ≤ Real.exp (Real.log z+(Real.log Q)*ε) := by
        apply Real.exp_le_exp.mpr
        have h1 := mul_le_mul_of_nonneg_left hNhi.le hlogz.le
        have h2 := mul_le_mul_of_nonneg_left hlogz' hlogQ.le
        nlinarith
      _ = _ := by rw [Real.exp_add,Real.exp_log hz0,Real.rpow_def_of_pos hQ0]
  have hR : 0 ≤ R := by
    by_contra! h
    have := mul_neg_of_neg_of_pos h (pow_pos hz0 N)
    linarith
  have hres' : (z-1)/2 ≤ R*(z*Q^ε) := hres.trans (mul_le_mul_of_nonneg_left hzpow hR)
  rw [Real.rpow_neg hQ0.le,←div_eq_mul_inv]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hQ0 ε)).mpr
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*z)).mpr
  nlinarith

open Complex Filter Topology Finset Set MeasureTheory

noncomputable def zetaRegular : ℂ → ℂ :=
  regularSeries (positiveCoefficients (fun _ => 1)) 1

lemma zetaRegular_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ zetaRegular s :=
  regularSeries_differentiableAt zero_le_one (fun _ ht => discrepancy_constant_bound ht.le) hs

lemma zetaRegular_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    zetaRegular s = riemannZeta s-1/(s-1) := by
  rw [zetaRegular,regularSeries_eq_LSeries_sub (positiveCoefficients_norm_le (by simp))
    zero_le_one (fun _ ht => discrepancy_constant_bound ht.le) hs,LSeries_positiveCoefficients]
  rw [show (fun _ : ℕ => (1:ℂ)) = 1 from rfl,LSeries_one_eq_riemannZeta hs]

lemma poleRemovedZeta_eq {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunctionTrivChar₁ 1 s = (s-1)*zetaRegular s+1 := by
  have hF : AnalyticOnNhd ℂ (DirichletCharacter.LFunctionTrivChar₁ 1) {s : ℂ | 0 < s.re} :=
    fun z _ => (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).analyticAt z
  have hG : AnalyticOnNhd ℂ (fun s : ℂ => (s-1)*zetaRegular s+1) {s : ℂ | 0 < s.re} := by
    apply DifferentiableOn.analyticOnNhd ?_ (continuous_re.isOpen_preimage _ isOpen_Ioi)
    intro z hz
    exact (((differentiableAt_id.sub_const 1).mul (zetaRegular_differentiableAt hz)).add_const 1).differentiableWithinAt
  have he : DirichletCharacter.LFunctionTrivChar₁ 1 =ᶠ[𝓝 (2:ℂ)]
      fun s : ℂ => (s-1)*zetaRegular s+1 := by
    filter_upwards [(continuous_re.tendsto (2:ℂ)).eventually
      (lt_mem_nhds (by norm_num : (1:ℝ) < (2:ℂ).re))] with z hz
    have hz1 : z ≠ 1 := by intro h; simp [h] at hz
    rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hz1,
      DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq,
      zetaRegular_eq_of_one_lt_re hz]
    field_simp
    ring
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG (convex_halfSpace_re_gt 0).isPreconnected
    (show (2:ℂ) ∈ {s : ℂ | 0 < s.re} by norm_num) he hs

lemma zetaRegular_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    zetaRegular s = riemannZeta s-1/(s-1) := by
  have h := poleRemovedZeta_eq hs
  rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hs1,
    DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq] at h
  have hn : s-1 ≠ 0 := sub_ne_zero.mpr hs1
  apply (mul_left_cancel₀ hn)
  rw [mul_sub,mul_div_cancel₀ _ hn]
  linear_combination -h

lemma regularSeries_norm_simple {f : ℕ → ℂ} {c : ℂ} {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    ‖regularSeries f c s‖ ≤ ‖c‖+‖s‖*D/s.re := by
  have h := discrepancyTail_norm_le zero_lt_one hD (measurable_seriesDiscrepancy f c) hb hs
  simp only [Real.one_rpow,mul_one] at h
  calc
    _ ≤ ‖c‖+‖s*discrepancyTail (seriesDiscrepancy f c) 1 s‖ := norm_add_le _ _
    _ ≤ ‖c‖+‖s‖*(D/s.re) := by rw [norm_mul]; gcongr
    _ = _ := by ring

lemma closedBall_two_re_norm {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    (1/4:ℝ) ≤ s.re ∧ ‖s‖ ≤ 4 := by
  have hd := Metric.mem_closedBall.mp hs
  have hr := Complex.re_le_norm ((2:ℂ)-s)
  rw [Complex.sub_re,←dist_eq_norm,dist_comm] at hr
  have hn : ‖s‖ ≤ dist s 2+‖(2:ℂ)‖ := by simpa [dist_eq_norm] using norm_add_le (s-2) (2:ℂ)
  norm_num at hr hn
  constructor <;> linarith

lemma zetaRegular_norm_le_seventeen {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    ‖zetaRegular s‖ ≤ 17 := by
  obtain ⟨hre,hnorm⟩ := closedBall_two_re_norm hs
  have hp : 0 < s.re := by linarith
  have h := regularSeries_norm_simple zero_le_one (fun _ ht => discrepancy_constant_bound ht.le) hp
  change ‖zetaRegular s‖ ≤ _ at h
  norm_num at h
  have hq : ‖s‖/s.re ≤ 16 := (div_le_iff₀ hp).mpr (by linarith)
  linarith

lemma LFunction_norm_polynomial {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    ‖χ.LFunction s‖ ≤ 16*((q:ℝ)+1) := by
  obtain ⟨hre,hnorm⟩ := closedBall_two_re_norm hs
  have hp : 0 < s.re := by linarith
  have hb := regularSeries_norm_simple (by positivity : (0:ℝ) ≤ q+1)
    (fun t _ => discrepancy_character_bound hχ t) hp
  rw [regularSeries_character_eq hχ hp] at hb
  simp only [norm_zero,zero_add] at hb
  apply hb.trans
  apply (div_le_iff₀ hp).mpr
  nlinarith [Nat.cast_nonneg (α:=ℝ) q]

noncomputable def regularizedZetaProduct (P : ℂ → ℂ) (s : ℂ) : ℂ :=
  zetaRegular s*P s+dslope P 1 s

lemma regularizedZetaProduct_differentiableOn {P : ℂ → ℂ}
    (hP : DifferentiableOn ℂ P {s : ℂ | 0 < s.re}) :
    DifferentiableOn ℂ (regularizedZetaProduct P) {s : ℂ | 0 < s.re} := by
  have hs : {s : ℂ | 0 < s.re} ∈ 𝓝 (1:ℂ) :=
    (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
  have hd := (Complex.differentiableOn_dslope hs).mpr hP
  have hz : DifferentiableOn ℂ zetaRegular {s : ℂ | 0 < s.re} :=
    fun s hs => (zetaRegular_differentiableAt hs).differentiableWithinAt
  exact (hz.mul hP).add hd

lemma regularizedZetaProduct_eq {P : ℂ → ℂ} {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    regularizedZetaProduct P s = riemannZeta s*P s-P 1/(s-1) := by
  rw [regularizedZetaProduct,zetaRegular_eq hs hs1,dslope_of_ne P hs1,slope_def_field]
  ring

lemma regularizedZetaProduct_bound {P : ℂ → ℂ} {B : ℝ}
    (hP : DifferentiableOn ℂ P {s : ℂ | 0 < s.re}) (_hB : 0 ≤ B)
    (hb : ∀ s ∈ Metric.closedBall (2:ℂ) (7/4:ℝ), ‖P s‖ ≤ B) :
    DiffContOnCl ℂ (regularizedZetaProduct P) (Metric.ball 2 (3/2:ℝ)) ∧
      ∀ s ∈ Metric.closedBall (2:ℂ) (3/2:ℝ), ‖regularizedZetaProduct P s‖ ≤ 21*B := by
  have hsRe (s : ℂ) (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) : 0 < s.re := by
    have := (closedBall_two_re_norm hs).1
    linarith
  have hder (s : ℂ) (hs : s ∈ Metric.closedBall 2 (3/2:ℝ)) : ‖deriv P s‖ ≤ 4*B := by
    have hsub : Metric.closedBall s (1/4:ℝ) ⊆ Metric.closedBall (2:ℂ) (7/4:ℝ) := by
      intro z hz
      have hdist := dist_triangle z s (2:ℂ)
      have hz' := Metric.mem_closedBall.mp hz
      have hs' := Metric.mem_closedBall.mp hs
      apply Metric.mem_closedBall.mpr
      linarith
    have hdiff : DiffContOnCl ℂ P (Metric.ball s (1/4:ℝ)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ (by norm_num : (1/4:ℝ) ≠ 0)]
      exact hP.mono (fun z hz => hsRe z (hsub hz))
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ) < 1/4)
      hdiff (fun z hz => hb z (hsub (Metric.sphere_subset_closedBall hz)))
    convert h using 1; ring
  have hone : (1:ℂ) ∈ Metric.closedBall (2:ℂ) (3/2:ℝ) := by
    norm_num [Metric.mem_closedBall,dist_eq_norm]
  have hdslope (s : ℂ) (hs : s ∈ Metric.closedBall 2 (3/2:ℝ)) : ‖dslope P 1 s‖ ≤ 4*B := by
    by_cases hs1 : s = 1
    · subst s
      simpa only [dslope_same] using hder 1 hone
    · rw [dslope_of_ne P hs1,slope_def_field,norm_div]
      have hd := (convex_closedBall (2:ℂ) (3/2:ℝ)).norm_image_sub_le_of_norm_deriv_le
        (fun z hz => (hP z (hsRe z (Metric.closedBall_subset_closedBall (by norm_num) hz))).differentiableAt
          ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
            (hsRe z (Metric.closedBall_subset_closedBall (by norm_num) hz)))) hder hone hs
      exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs1))).mpr hd
  constructor
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (by norm_num : (3/2:ℝ) ≠ 0)]
    exact (regularizedZetaProduct_differentiableOn hP).mono
      (fun z hz => hsRe z (Metric.closedBall_subset_closedBall (by norm_num) hz))
  · intro s hs
    have hs' := Metric.closedBall_subset_closedBall (by norm_num : (3/2:ℝ) ≤ 7/4) hs
    calc
      _ ≤ ‖zetaRegular s*P s‖+‖dslope P 1 s‖ := norm_add_le _ _
      _ ≤ 17*B+4*B := by rw [norm_mul]; gcongr; exact zetaRegular_norm_le_seventeen hs'; exact hb s hs'; exact hdslope s hs
      _ = _ := by ring

open Complex Finset ArithmeticFunction

open scoped ComplexOrder

def PrimePowerEq (p : ℕ) (f g : ArithmeticFunction ℂ) : Prop :=
  ∀ k : ℕ, f (p^k) = g (p^k)

lemma PrimePowerEq.refl (p : ℕ) (f : ArithmeticFunction ℂ) : PrimePowerEq p f f := fun _ => rfl

lemma PrimePowerEq.mul {p : ℕ} (hp : p.Prime) {f f' g g' : ArithmeticFunction ℂ}
    (hf : PrimePowerEq p f f') (hg : PrimePowerEq p g g') : PrimePowerEq p (f*g) (f'*g') := by
  intro k
  simp only [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨i,hi,hxi⟩ := (Nat.dvd_prime_pow hp).mp (Nat.mem_divisors.mp
    (Nat.fst_mem_divisors_of_mem_antidiagonal hx)).1
  obtain ⟨j,hj,hxj⟩ := (Nat.dvd_prime_pow hp).mp (Nat.mem_divisors.mp
    (Nat.snd_mem_divisors_of_mem_antidiagonal hx)).1
  rw [hxi,hxj,hf,hg]

lemma primePower_zeta {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (p^k) = 1 := by
  simp [hp.ne_zero]

lemma primePower_one {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (1 : ArithmeticFunction ℂ) (p^k) = (0:ℂ)^k := by
  cases k with
  | zero => simp
  | succ k =>
    have hn : p^(k+1) ≠ 1 := by
      have h : 1 < p^(k+1) := one_lt_pow₀ hp.one_lt (by omega)
      omega
    simp [hp.ne_one]

lemma primePower_character {q p : ℕ} (χ : DirichletCharacter ℂ q) (hp : p.Prime) (k : ℕ) :
    toArithmeticFunction (χ ·) (p^k) = χ (p : ZMod q)^k := by
  simp [toArithmeticFunction,hp.ne_zero]

lemma arithmetic_convolution_nonneg {f g : ArithmeticFunction ℂ}
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (n : ℕ) : 0 ≤ (f*g) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hf x.1) (hg x.2))

noncomputable def biquadraticCoefficients {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) : ArithmeticFunction ℂ :=
  ArithmeticFunction.zeta * toArithmeticFunction (χ ·) * toArithmeticFunction (ψ ·) *
    (toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·))

lemma biquadraticCoefficients_multiplicative {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    (biquadraticCoefficients χ ψ).IsMultiplicative := by
  exact ((isMultiplicative_zeta.natCast.mul (DirichletCharacter.isMultiplicative_toArithmeticFunction χ)).mul
    (DirichletCharacter.isMultiplicative_toArithmeticFunction ψ)).mul
    ((DirichletCharacter.isMultiplicative_toArithmeticFunction χ).pmul (DirichletCharacter.isMultiplicative_toArithmeticFunction ψ))

lemma biquadraticCoefficients_comm {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    biquadraticCoefficients χ ψ = biquadraticCoefficients ψ χ := by
  unfold biquadraticCoefficients
  rw [ArithmeticFunction.pmul_comm]
  ring

lemma biquadratic_prime_zero {q r p : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (hp : p.Prime)
    (hχ : χ (p : ZMod q) = 0) :
    PrimePowerEq p (biquadraticCoefficients χ ψ) ψ.zetaMul := by
  have hf : PrimePowerEq p (toArithmeticFunction (χ ·)) 1 := by
    intro k
    rw [primePower_character χ hp, hχ,primePower_one hp]
  have hh : PrimePowerEq p ((toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·))) 1 := by
    intro k
    rw [ArithmeticFunction.pmul_apply,primePower_character χ hp,primePower_character ψ hp,
      hχ,←mul_pow,zero_mul,primePower_one hp]
  have h := ((PrimePowerEq.refl p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)).mul hp hf).mul hp
    (PrimePowerEq.refl p (toArithmeticFunction (ψ ·))) |>.mul hp hh
  simpa only [mul_one,biquadraticCoefficients,DirichletCharacter.zetaMul] using h

lemma biquadratic_prime_one {q r p : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (hp : p.Prime)
    (hχ : χ (p : ZMod q) = 1) :
    PrimePowerEq p (biquadraticCoefficients χ ψ) (ψ.zetaMul*ψ.zetaMul) := by
  have hf : PrimePowerEq p (toArithmeticFunction (χ ·)) ArithmeticFunction.zeta := by
    intro k
    rw [primePower_character χ hp,hχ,one_pow,primePower_zeta hp]
  have hh : PrimePowerEq p ((toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·)))
      (toArithmeticFunction (ψ ·)) := by
    intro k
    rw [ArithmeticFunction.pmul_apply,primePower_character χ hp,hχ,one_pow,one_mul]
  have h := ((PrimePowerEq.refl p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)).mul hp hf).mul hp
    (PrimePowerEq.refl p (toArithmeticFunction (ψ ·))) |>.mul hp hh
  have he : (ArithmeticFunction.zeta : ArithmeticFunction ℂ)*ArithmeticFunction.zeta*
      toArithmeticFunction (ψ ·)*toArithmeticFunction (ψ ·) = ψ.zetaMul*ψ.zetaMul := by
    unfold DirichletCharacter.zetaMul
    ring
  simpa only [he,biquadraticCoefficients] using h

lemma biquadratic_prime_neg_one {q r p : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (hp : p.Prime)
    (hχ : χ (p : ZMod q) = -1) (hψ : ψ (p : ZMod r) = -1) :
    PrimePowerEq p (biquadraticCoefficients χ ψ) (χ.zetaMul*χ.zetaMul) := by
  have hg : PrimePowerEq p (toArithmeticFunction (ψ ·)) (toArithmeticFunction (χ ·)) := by
    intro k
    rw [primePower_character ψ hp,primePower_character χ hp,hχ,hψ]
  have hh : PrimePowerEq p ((toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·)))
      ArithmeticFunction.zeta := by
    intro k
    rw [ArithmeticFunction.pmul_apply,primePower_character χ hp,primePower_character ψ hp,
      hχ,hψ,←mul_pow,neg_mul_neg,one_mul,one_pow,primePower_zeta hp]
  have h := ((PrimePowerEq.refl p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)).mul hp
    (PrimePowerEq.refl p (toArithmeticFunction (χ ·)))).mul hp hg |>.mul hp hh
  have he : (ArithmeticFunction.zeta : ArithmeticFunction ℂ)*toArithmeticFunction (χ ·)*
      toArithmeticFunction (χ ·)*ArithmeticFunction.zeta = χ.zetaMul*χ.zetaMul := by
    unfold DirichletCharacter.zetaMul
    ring
  simpa only [he,biquadraticCoefficients] using h

lemma biquadraticCoefficients_nonneg {q r : ℕ} {χ : DirichletCharacter ℂ q}
    {ψ : DirichletCharacter ℂ r} (hχ : χ^2=1) (hψ : ψ^2=1) (n : ℕ) :
    0 ≤ biquadraticCoefficients χ ψ n := by
  have hp (p : ℕ) (hp : p.Prime) (k : ℕ) : 0 ≤ biquadraticCoefficients χ ψ (p^k) := by
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ (p:ZMod q) with h0|h1|hm
    · rw [biquadratic_prime_zero χ ψ hp h0 k]
      exact DirichletCharacter.zetaMul_nonneg hψ _
    · rw [biquadratic_prime_one χ ψ hp h1 k]
      exact arithmetic_convolution_nonneg (DirichletCharacter.zetaMul_nonneg hψ)
        (DirichletCharacter.zetaMul_nonneg hψ) _
    · rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hψ (p:ZMod r) with h0|h1|hm'
      · rw [biquadraticCoefficients_comm χ ψ,biquadratic_prime_zero ψ χ hp h0 k]
        exact DirichletCharacter.zetaMul_nonneg hχ _
      · rw [biquadraticCoefficients_comm χ ψ,biquadratic_prime_one ψ χ hp h1 k]
        exact arithmetic_convolution_nonneg (DirichletCharacter.zetaMul_nonneg hχ)
          (DirichletCharacter.zetaMul_nonneg hχ) _
      · rw [biquadratic_prime_neg_one χ ψ hp hm hm' k]
        exact arithmetic_convolution_nonneg (DirichletCharacter.zetaMul_nonneg hχ)
          (DirichletCharacter.zetaMul_nonneg hχ) _
  rcases eq_or_ne n 0 with rfl|hn
  · simp
  · simpa only [(biquadraticCoefficients_multiplicative χ ψ).multiplicative_factorization _ hn,
      Finsupp.prod, Nat.support_factorization] using
      Finset.prod_nonneg (fun p hp' => hp p (Nat.prime_of_mem_primeFactors hp') _)

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_TaylorBounds

section File_OpenAIPrimeGaps_SiegelBounds

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

section

open Complex Filter Topology Set MeasureTheory Finset ArithmeticFunction

lemma quadratic_character_im {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ^2=1)
    (a : ZMod q) : (χ a).im = 0 := by
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ a with h|h|h <;> simp [h]

lemma regularSeries_im_zero {f : ℕ → ℂ} {c : ℂ} {D : ℝ}
    (hf : ∀ n, (f n).im=0) (hc : c.im=0) (hD : 0 ≤ D)
    (hb : ∀ t, 1<t → ‖seriesDiscrepancy f c t‖ ≤ D) {x : ℝ} (hx : 0<x) :
    (regularSeries f c x).im=0 := by
  have hi := discrepancyTail_integrable zero_lt_one hD (measurable_seriesDiscrepancy f c) hb
    (show 0<(x:ℂ).re from hx)
  have he : (discrepancyTail (seriesDiscrepancy f c) 1 x).im=0 := by
    unfold discrepancyTail
    change RCLike.im (∫ t in Ioi (1:ℝ), seriesDiscrepancy f c t*(t:ℂ)^(-((x:ℂ)+1)))=0
    rw [←integral_im hi]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hp : ((t:ℂ)^(-((x:ℂ)+1))).im=0 := by
      rw [show -((x:ℂ)+1)= (-(x+1):ℝ) by push_cast; rfl,
        ←Complex.ofReal_cpow (by exact (zero_lt_one.trans ht).le : 0≤t)]
      rfl
    change (seriesDiscrepancy f c t * (t:ℂ)^(-((x:ℂ)+1))).im=0
    rw [Complex.mul_im,hp,mul_zero,zero_add]
    have hz : (seriesDiscrepancy f c t).im=0 := by simp [seriesDiscrepancy,Complex.mul_im,hc,hf]
    rw [hz,zero_mul]
  simp [regularSeries,Complex.mul_im,hc,he]

lemma quadratic_LFunction_im {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) (hχ2 : χ^2=1) {x : ℝ} (hx : 0<x) : (χ.LFunction x).im=0 := by
  rw [←regularSeries_character_eq hχ hx]
  apply regularSeries_im_zero _ (by simp) (by positivity : (0:ℝ)≤q+1)
    (fun t _ => discrepancy_character_bound hχ t) hx
  intro n
  simp only [positiveCoefficients]
  split_ifs <;> simp [quadratic_character_im hχ2]

lemma LSeries_character_summable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (toArithmeticFunction (fun n : ℕ => χ (n : ZMod q))) s := by
  apply (LSeriesSummable_congr _ (fun h => (χ.apply_eq_toArithmeticFunction_apply h).symm)).mpr
  exact ZMod.LSeriesSummable_of_one_lt_re χ hs

lemma LSeries_character_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    LSeries (toArithmeticFunction (fun n : ℕ => χ (n : ZMod q))) s = χ.LFunction s := by
  rw [χ.LFunction_eq_LSeries hs]
  exact (LSeries_congr χ.apply_eq_toArithmeticFunction_apply s).symm

lemma LSeries_zeta_complex_eq {s : ℂ} (hs : 1<s.re) :
    LSeries (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s=riemannZeta s := by
  rw [←LSeries_one_eq_riemannZeta hs]
  apply LSeries_congr
  intro n hn
  simp [hn]

lemma LSeries_zetaMul_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) : LSeries χ.zetaMul s=riemannZeta s*χ.LFunction s := by
  have hz : LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m:=1) _ hs
    intro n hn
    simp [hn]
  rw [DirichletCharacter.zetaMul,ArithmeticFunction.LSeries_mul' hz
    (LSeries_character_summable χ hs),LSeries_character_eq χ hs,LSeries_zeta_complex_eq hs]

open scoped ComplexOrder in
lemma quadratic_LFunction_re_pos_of_one_lt {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ2 : χ^2=1) {x : ℝ} (hx : 1<x) :
    0<(χ.LFunction x).re := by
  have hp := LSeries.positive (DirichletCharacter.zetaMul_nonneg hχ2)
    (χ.isMultiplicative_zetaMul.map_one ▸ zero_lt_one)
    (lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun s hs => χ.LSeriesSummable_zetaMul hs)) (show (1:EReal)<x by exact_mod_cast hx))
  rw [LSeries_zetaMul_eq χ hx] at hp
  have hr := (Complex.pos_iff.mp hp).1
  rw [Complex.mul_re,riemannZeta_im_eq_zero_of_one_lt hx,zero_mul,sub_zero] at hr
  exact (mul_pos_iff.mp hr).resolve_right (fun h => (riemannZeta_re_pos_of_one_lt hx).not_ge h.1.le) |>.2

lemma quadratic_LFunction_re_pos_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) (hχ2 : χ^2=1) : 0<(χ.LFunction 1).re := by
  have hc : Continuous (fun x : ℝ => (χ.LFunction x).re) :=
    Complex.continuous_re.comp ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal)
  have hn : 0≤(χ.LFunction 1).re := by
    apply ge_of_tendsto (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto (fun x : ℝ => (χ.LFunction x).re) (𝓝[>] 1) (𝓝 ((χ.LFunction 1).re)))
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (quadratic_LFunction_re_pos_of_one_lt hχ2 hx).le
  refine lt_of_le_of_ne hn ?_
  intro he
  apply DirichletCharacter.LFunction_apply_one_ne_zero hχ
  apply Complex.ext
  · simpa using he.symm
  · simpa using quadratic_LFunction_im hχ hχ2 (x:=1) zero_lt_one

lemma quadratic_LFunction_re_pos_of_no_root {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ≠1) (hχ2 : χ^2=1)
    {β : ℝ} (hβ : 0<β) (hβ1 : β≤1)
    (hz : ∀ x ∈ Set.Icc β 1, χ.LFunction x≠0) : 0<(χ.LFunction β).re := by
  by_contra! hn
  have hc : Continuous (fun x : ℝ => (χ.LFunction x).re) :=
    Complex.continuous_re.comp ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal)
  obtain ⟨x,hx,hxe⟩ := intermediate_value_Icc hβ1 hc.continuousOn
    (show (0:ℝ) ∈ Set.Icc ((χ.LFunction β).re) ((χ.LFunction 1).re) from
      ⟨hn,(quadratic_LFunction_re_pos_one hχ hχ2).le⟩)
  apply hz x hx
  apply Complex.ext
  · simpa using hxe
  · simpa using quadratic_LFunction_im hχ hχ2 (hβ.trans_le hx.1)

end

section

open Complex Finset ArithmeticFunction

noncomputable def productCharacter {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : DirichletCharacter ℂ (q*r) :=
  χ.changeLevel (dvd_mul_right q r) * ψ.changeLevel (dvd_mul_left r q)

lemma changeLevel_natCast {q m : ℕ} (χ : DirichletCharacter ℂ q) (hqm : q∣m)
    {n : ℕ} (hn : n.Coprime m) :
    χ.changeLevel hqm (n : ZMod m)=χ (n : ZMod q) := by
  have h := χ.changeLevel_eq_cast_of_dvd hqm (ZMod.unitOfCoprime n hn)
  simp only [ZMod.coe_unitOfCoprime] at h
  rw [ZMod.cast_natCast hqm] at h
  exact h

lemma productCharacter_apply {q r n : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : productCharacter χ ψ (n : ZMod (q*r))=
      χ (n : ZMod q)*ψ (n : ZMod r) := by
  by_cases hn : n.Coprime (q*r)
  · simp only [productCharacter,MulChar.mul_apply,changeLevel_natCast _ _ hn]
  · rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])]
    by_cases hq : n.Coprime q
    · have hr : ¬n.Coprime r := fun hr => hn (hq.mul_right hr)
      rw [ψ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime]),mul_zero]
    · rw [χ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime]),zero_mul]

lemma productCharacter_quadratic {q r : ℕ} {χ : DirichletCharacter ℂ q}
    {ψ : DirichletCharacter ℂ r} (hχ : χ^2=1) (hψ : ψ^2=1) :
    (productCharacter χ ψ)^2=1 := by
  simp [productCharacter,mul_pow,←map_pow,hχ,hψ]

lemma productCharacter_ne_one_of_levels_ne {q r : ℕ} [NeZero q] [NeZero r]
    {χ : DirichletCharacter ℂ q} {ψ : DirichletCharacter ℂ r}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hψ2 : ψ^2=1) (hqr : q≠r) :
    productCharacter χ ψ≠1 := by
  intro h
  have h2 : (ψ.changeLevel (dvd_mul_left r q))^2=1 := by rw [←map_pow,hψ2,map_one]
  have he : χ.changeLevel (dvd_mul_right q r) = ψ.changeLevel (dvd_mul_left r q) := by
    calc
      _ = (χ.changeLevel (dvd_mul_right q r)*ψ.changeLevel (dvd_mul_left r q))*
          ψ.changeLevel (dvd_mul_left r q) := by rw [mul_assoc,←pow_two,h2,mul_one]
      _ = _ := by rw [show χ.changeLevel (dvd_mul_right q r)*ψ.changeLevel (dvd_mul_left r q)=1 from h,one_mul]
  have hc := congrArg DirichletCharacter.conductor he
  rw [DirichletCharacter.conductor_changeLevel,DirichletCharacter.conductor_changeLevel,
    hχ,hψ] at hc
  exact hqr hc

lemma productCharacter_toArithmeticFunction {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) :
    toArithmeticFunction (productCharacter χ ψ ·)=
      (toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·)) := by
  ext n
  by_cases hn : n=0
  · simp [hn]
  · rw [ArithmeticFunction.pmul_apply]
    simp [toArithmeticFunction,hn,productCharacter_apply]

end

section

open Complex Filter Topology Set MeasureTheory Finset

open scoped ComplexOrder in
lemma zeta_product_residue_lower {P : ℂ → ℂ} {a : ℕ → ℂ} {A B Q β ε : ℝ}
    (hP : DifferentiableOn ℂ P {s : ℂ | 0<s.re})
    (hB : 0≤B) (hb : ∀ s ∈ Metric.closedBall (2:ℂ) (7/4:ℝ), ‖P s‖≤B)
    (hA : 0≤A) (hQ : 2≤Q) (hQA : 12*A≤Q) (hBQ : 21*B≤A*Q^4)
    (hβ : 3/4≤β) (hβ1 : β<1) (hβε : 60*(1-β)≤ε)
    (ha : ∀ n, 0≤a n) (ha1 : 1≤a 1) (haC : LSeries.abscissaOfAbsConv a≤1)
    (haP : ∀ s : ℂ, 1<s.re → LSeries a s=riemannZeta s*P s)
    (hvalue : (riemannZeta β*P β).re≤0) (hreal : (P 1).im=0) :
    ((1-β)/(2*(2-β)))*Q^(-ε)≤(P 1).re := by
  let H := regularizedZetaProduct P
  have hR : P 1=((P 1).re:ℂ) := by apply Complex.ext <;> simp [hreal]
  obtain ⟨hf,hbound⟩ := regularizedZetaProduct_bound hP hB hb
  have he : H =ᶠ[𝓝 (2:ℂ)] fun s => LSeries a s-((P 1).re:ℂ)/(s-1) := by
    filter_upwards [(continuous_re.tendsto (2:ℂ)).eventually
      (lt_mem_nhds (by norm_num : (1:ℝ)<(2:ℂ).re))] with s hs
    have hs1 : s≠1 := by intro h; simp [h] at hs
    rw [show H s=regularizedZetaProduct P s from rfl,regularizedZetaProduct_eq (by linarith) hs1,
      ←haP s hs,hR]
    simp only [Complex.ofReal_re]
  have hac : LSeries.abscissaOfAbsConv a<(2:ℝ) := haC.trans_lt (by exact_mod_cast (show (1:ℝ)<2 by norm_num))
  obtain ⟨ha0,han⟩ := signedTaylorCoeff_regular_nonneg ha ha1 hac he
  have hz : 1<2-β := by linarith
  have hz0 : 0<2-β := by linarith
  have hzr : 2-β<(3/2:ℝ) := by linarith
  have hv : (∑' n : ℕ, signedTaylorCoeff H n*(2-β)^n)≤(P 1).re/((2-β)-1) := by
    rw [(signedTaylorCoeff_hasSum hf.differentiableOn (by rwa [abs_of_pos hz0])).tsum_eq]
    have hβ0 : 0<β := by linarith
    have hβne : (β:ℂ)≠1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [show (2-(2-β):ℝ)=β by ring]
    change (regularizedZetaProduct P β).re≤_
    rw [regularizedZetaProduct_eq hβ0 hβne,Complex.sub_re,hR,
      ←Complex.ofReal_one,←Complex.ofReal_sub,←Complex.ofReal_div,Complex.ofReal_re]
    have hid : (P 1).re/(β-1) = -(P 1).re/((2-β)-1) := by
      rw [show β-1 = -((2-β)-1) by ring,div_neg,neg_div]
    simp only [Complex.ofReal_one,Complex.ofReal_re]
    rw [hid,neg_div,sub_neg_eq_add]
    exact add_le_of_nonpos_left hvalue
  have hn (n : ℕ) : |signedTaylorCoeff H n|≤(A*Q^4)/(3/2)^n := by
    apply (signedTaylorCoeff_norm_bound (by norm_num : (0:ℝ)<3/2) hf
      (fun s hs => (hbound s (Metric.sphere_subset_closedBall hs)).trans hBQ) n)
  have hr := residue_polynomial_lower (ε:=ε) hA hQ hQA hz (by linarith) (by linarith) hn
    (by simpa [signedTaylorCoeff] using ha0) han hv
  convert hr using 1
  congr 2
  ring

lemma zeta_re_neg_near_one {β : ℝ} (hβ : 99/100≤β) (hβ1 : β<1) :
    (riemannZeta β).re<0 := by
  have hβ0 : 0<β := by linarith
  have hβne : (β:ℂ)≠1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hmem : (β:ℂ) ∈ Metric.closedBall 2 (7/4:ℝ) := by
    rw [Metric.mem_closedBall,dist_eq_norm,←Complex.ofReal_ofNat,←Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,abs_of_neg (by linarith : β-2<0)]
    linarith
  have hb := (Complex.re_le_norm (zetaRegular β)).trans (zetaRegular_norm_le_seventeen hmem)
  rw [zetaRegular_eq hβ0 hβne,Complex.sub_re,←Complex.ofReal_one,
    ←Complex.ofReal_sub,←Complex.ofReal_div,Complex.ofReal_re] at hb
  have hd : 1/(β-1)≤-100 := (div_le_iff_of_neg (by linarith : β-1<0)).mpr (by linarith)
  linarith

end

open Complex Filter Topology Set MeasureTheory Finset ArithmeticFunction

lemma LSeries_zeta_complex_summable {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m:=1) _ hs
  intro n hn
  simp [hn]

lemma biquadraticCoefficients_summable {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (biquadraticCoefficients χ ψ) s := by
  rw [biquadraticCoefficients,←productCharacter_toArithmeticFunction]
  exact ArithmeticFunction.LSeriesSummable_mul
    (ArithmeticFunction.LSeriesSummable_mul
      (ArithmeticFunction.LSeriesSummable_mul (LSeries_zeta_complex_summable hs) (LSeries_character_summable χ hs))
      (LSeries_character_summable ψ hs)) (LSeries_character_summable (productCharacter χ ψ) hs)

lemma LSeries_biquadratic_eq {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) {s : ℂ} (hs : 1<s.re) :
    LSeries (biquadraticCoefficients χ ψ) s=
      riemannZeta s*(χ.LFunction s*ψ.LFunction s*(productCharacter χ ψ).LFunction s) := by
  have hz := LSeries_zeta_complex_summable hs
  have hχ := LSeries_character_summable χ hs
  have hψ := LSeries_character_summable ψ hs
  have hp := LSeries_character_summable (productCharacter χ ψ) hs
  rw [biquadraticCoefficients,←productCharacter_toArithmeticFunction,
    ArithmeticFunction.LSeries_mul' (ArithmeticFunction.LSeriesSummable_mul (ArithmeticFunction.LSeriesSummable_mul hz hχ) hψ) hp,
    ArithmeticFunction.LSeries_mul' (ArithmeticFunction.LSeriesSummable_mul hz hχ) hψ,
    ArithmeticFunction.LSeries_mul' hz hχ,LSeries_zeta_complex_eq hs,
    LSeries_character_eq χ hs,LSeries_character_eq ψ hs,
    LSeries_character_eq (productCharacter χ ψ) hs]
  ring

lemma quadratic_residue_lower_of_no_root {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ≠1) (hχ2 : χ^2=1)
    {β ε : ℝ} (hβ : 99/100≤β) (hβ1 : β<1) (hβε : 60*(1-β)≤ε)
    (hq : (4032:ℝ)≤q+1) (hz : ∀ x ∈ Set.Icc β 1, χ.LFunction x≠0) :
    ((1-β)/(2*(2-β)))*((q:ℝ)+1)^(-ε)≤‖χ.LFunction 1‖ := by
  have hQ : (2:ℝ)≤q+1 := by linarith
  have hpow : (q:ℝ)+1≤((q:ℝ)+1)^4 := le_self_pow₀ (by linarith) (by norm_num)
  have hv : (riemannZeta β*χ.LFunction β).re≤0 := by
    rw [Complex.mul_re,quadratic_LFunction_im hχ hχ2 (by linarith),mul_zero,sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (zeta_re_neg_near_one hβ hβ1).le
      (quadratic_LFunction_re_pos_of_no_root hχ hχ2 (by linarith) hβ1.le hz).le
  apply le_trans _ (Complex.re_le_norm _)
  apply zeta_product_residue_lower (a:=χ.zetaMul) (A:=336) (B:=16*((q:ℝ)+1))
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn (by positivity)
    (fun s hs => LFunction_norm_polynomial hχ hs) (by norm_num) hQ
    (by norm_num; exact hq) (by nlinarith) (by linarith) hβ1 hβε
    (DirichletCharacter.zetaMul_nonneg hχ2)
    (by simp only [χ.isMultiplicative_zetaMul.map_one,le_refl])
    (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (fun s hs => χ.LSeriesSummable_zetaMul hs))
    (fun s hs => LSeries_zetaMul_eq χ hs) hv
    (by simpa using quadratic_LFunction_im hχ hχ2 (x:=1) zero_lt_one)

lemma biquadratic_norm_bound {q r : ℕ} [NeZero q] [NeZero r]
    {χ : DirichletCharacter ℂ q} {ψ : DirichletCharacter ℂ r}
    (hχ : χ≠1) (hψ : ψ≠1) (hp : productCharacter χ ψ≠1)
    {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    ‖χ.LFunction s*ψ.LFunction s*(productCharacter χ ψ).LFunction s‖≤
      16^3*((q:ℝ)+1)^2*((r:ℝ)+1)^2 := by
  have hq0 : (0:ℝ)≤q := Nat.cast_nonneg q
  have hr0 : (0:ℝ)≤r := Nat.cast_nonneg r
  have hp' := LFunction_norm_polynomial hp hs
  simp only [Nat.cast_mul] at hp'
  calc
    _ ≤ (16*((q:ℝ)+1))*(16*((r:ℝ)+1))*(16*((q:ℝ)*r+1)) := by
      simp only [norm_mul]
      gcongr
      · exact LFunction_norm_polynomial hχ hs
      · exact LFunction_norm_polynomial hψ hs
    _ ≤ _ := by nlinarith [mul_nonneg hq0 hr0]

lemma biquadratic_residue_lower_of_root {q r : ℕ} [NeZero q] [NeZero r]
    {χ : DirichletCharacter ℂ q} {ψ : DirichletCharacter ℂ r}
    (hχ : χ≠1) (hχ2 : χ^2=1) (hψ : ψ≠1) (hψ2 : ψ^2=1)
    (hp : productCharacter ψ χ≠1) {β ε : ℝ}
    (hβ : 3/4≤β) (hβ1 : β<1) (hβε : 60*(1-β)≤ε)
    (hq : (12*(21*16^3*((r:ℝ)+1)^2))≤q+1) (hq1 : (2:ℝ)≤q+1)
    (hz : ψ.LFunction β=0) :
    ((1-β)/(2*(2-β)))*((q:ℝ)+1)^(-ε)≤
      ‖ψ.LFunction 1‖*‖χ.LFunction 1‖*‖(productCharacter ψ χ).LFunction 1‖ := by
  let P := fun s => ψ.LFunction s*χ.LFunction s*(productCharacter ψ χ).LFunction s
  have hd : Differentiable ℂ P :=
    ((DirichletCharacter.differentiable_LFunction hψ).mul
      (DirichletCharacter.differentiable_LFunction hχ)).mul
      (DirichletCharacter.differentiable_LFunction hp)
  have hpow : ((q:ℝ)+1)^2≤((q:ℝ)+1)^4 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have hb : ∀ s ∈ Metric.closedBall (2:ℂ) (7/4:ℝ),
      ‖P s‖≤16^3*((r:ℝ)+1)^2*((q:ℝ)+1)^2 := fun s hs => biquadratic_norm_bound hψ hχ hp hs
  have hiψ : (ψ.LFunction 1).im=0 := by simpa using quadratic_LFunction_im hψ hψ2 (x:=1) zero_lt_one
  have hiχ : (χ.LFunction 1).im=0 := by simpa using quadratic_LFunction_im hχ hχ2 (x:=1) zero_lt_one
  have hip : ((productCharacter ψ χ).LFunction 1).im=0 := by
    simpa using quadratic_LFunction_im hp (productCharacter_quadratic hψ2 hχ2) (x:=1) zero_lt_one
  have hreal : (P 1).im=0 := by simp [P,Complex.mul_im,hiψ,hiχ,hip]
  have hR := zeta_product_residue_lower (P:=P) (a:=biquadraticCoefficients ψ χ)
    (A:=21*16^3*((r:ℝ)+1)^2) (B:=16^3*((r:ℝ)+1)^2*((q:ℝ)+1)^2)
    hd.differentiableOn (by positivity) hb (by positivity) hq1 hq
    (by nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ)≤21*16^3*((r:ℝ)+1)^2)])
    hβ hβ1 hβε (biquadraticCoefficients_nonneg hψ2 hχ2)
    (by simp only [(biquadraticCoefficients_multiplicative ψ χ).map_one,le_refl])
    (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun s hs => biquadraticCoefficients_summable ψ χ hs))
    (fun s hs => LSeries_biquadratic_eq ψ χ hs) (by simp [P,hz]) hreal
  have := hR.trans (Complex.re_le_norm (P 1))
  simpa only [P,norm_mul] using this

lemma quadratic_siegel_eventual {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c Q₀ : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → χ^2=1 → Q₀≤(q:ℝ)+1 → c*((q:ℝ)+1)^(-ε)≤‖χ.LFunction 1‖ := by
  classical
  let β₀ : ℝ := 1-ε/240
  have hβ₀ : 99/100≤β₀ := by dsimp [β₀]; linarith
  have hβ₀1 : β₀<1 := by dsimp [β₀]; linarith
  by_cases hex : ∃ r : ℕ, ∃ ψ : DirichletCharacter ℂ (r+1),
      ψ.IsPrimitive ∧ ψ≠1 ∧ ψ^2=1 ∧ ∃ β ∈ Set.Icc β₀ 1, ψ.LFunction β=0
  · obtain ⟨r,ψ,hψprim,hψ,hψ2,β,hβI,hzero⟩ := hex
    have hβ1 : β<1 := lt_of_le_of_ne hβI.2 (by
      intro he
      apply DirichletCharacter.LFunction_apply_one_ne_zero hψ
      simpa [he] using hzero)
    have hβ : 99/100≤β := hβ₀.trans hβI.1
    have hβε : 60*(1-β)≤ε/2 := by dsimp [β₀] at hβI; linarith [hβI.1]
    obtain ⟨K,hK,hgrowth⟩ := LFunction_norm_small_power (by linarith : 0<ε/4)
      (by linarith : ε/4≤1/2)
    let D : ℝ := 3*((r:ℝ)+3)
    let U : ℝ := ‖ψ.LFunction 1‖*K*D^(ε/2)
    have hD : 0<D := by dsimp [D]; positivity
    have hU : 0<U := by
      exact mul_pos (mul_pos (norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero hψ)) hK)
        (Real.rpow_pos_of_pos hD _)
    let c : ℝ := (1-β)/(2*(2-β))/U
    have hc : 0<c := div_pos (div_pos (by linarith) (by linarith)) hU
    refine ⟨c,max (12*(21*16^3*(((r+1:ℕ):ℝ)+1)^2)) ((r:ℝ)+3),hc,?_⟩
    intro q _ χ hχprim hχ hχ2 hq
    have hq1 : (2:ℝ)≤q+1 := by have := (le_max_right _ _).trans hq; have : (0:ℝ)≤r := Nat.cast_nonneg r; linarith
    have hqr : r+1≠q := by
      have hr := (le_max_right _ _).trans hq
      intro he
      rw [←he] at hr
      push_cast at hr
      linarith
    have hp : productCharacter ψ χ≠1 :=
      productCharacter_ne_one_of_levels_ne hψprim hχprim hχ2 hqr
    have hl := biquadratic_residue_lower_of_root hχ hχ2 hψ hψ2 hp
      (by linarith) hβ1 hβε ((le_max_left _ _).trans hq) hq1 hzero
    have hb := hgrowth ((r+1)*q) (productCharacter ψ χ) hp 1 (by simp; linarith)
    have hQ0 : 0<(q:ℝ)+1 := by positivity
    have he : 2*(ε/4)=ε/2 := by ring
    rw [he] at hb
    have hbase : (((r+1)*q:ℕ):ℝ)+2≤((r:ℝ)+3)*((q:ℝ)+1) := by push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) q,Nat.cast_nonneg (α:=ℝ) r]
    have hb' : ‖(productCharacter ψ χ).LFunction 1‖≤K*D^(ε/2)*((q:ℝ)+1)^(ε/2) := by
      apply hb.trans
      simp only [norm_one]
      calc
        K*(((((r+1)*q:ℕ):ℝ)+2)*(1+2))^(ε/2) ≤ K*(D*((q:ℝ)+1))^(ε/2) := by
          apply mul_le_mul_of_nonneg_left _ hK.le
          apply Real.rpow_le_rpow (by positivity) _ (by linarith)
          dsimp [D]
          nlinarith
        _ = _ := by rw [Real.mul_rpow hD.le hQ0.le]; ring
    have hupper : ‖ψ.LFunction 1‖*‖χ.LFunction 1‖*‖(productCharacter ψ χ).LFunction 1‖≤
        U*((q:ℝ)+1)^(ε/2)*‖χ.LFunction 1‖ := by
      calc
        _ ≤ ‖ψ.LFunction 1‖*‖χ.LFunction 1‖*(K*D^(ε/2)*((q:ℝ)+1)^(ε/2)) := by gcongr
        _ = _ := by dsimp [U]; ring
    have hlow := hl.trans hupper
    have hQp : 0<((q:ℝ)+1)^(ε/2) := Real.rpow_pos_of_pos hQ0 _
    have hexp : ((q:ℝ)+1)^(-ε)*((q:ℝ)+1)^(ε/2)=((q:ℝ)+1)^(-(ε/2)) := by
      rw [←Real.rpow_add hQ0]; congr 1; ring
    have hfinal : U*(c*((q:ℝ)+1)^(-ε)*((q:ℝ)+1)^(ε/2)) ≤
        U*(‖χ.LFunction 1‖*((q:ℝ)+1)^(ε/2)) := by
      calc
        U*(c*((q:ℝ)+1)^(-ε)*((q:ℝ)+1)^(ε/2)) =
            ((1-β)/(2*(2-β)))*((q:ℝ)+1)^(-(ε/2)) := by
          rw [mul_assoc c,hexp]
          dsimp [c]
          field_simp
        _ ≤ U*(‖χ.LFunction 1‖*((q:ℝ)+1)^(ε/2)) := by simpa only [mul_assoc,mul_left_comm,mul_comm] using hlow
    exact (mul_le_mul_iff_left₀ hQp).mp ((mul_le_mul_iff_right₀ hU).mp hfinal)
  · refine ⟨(1-β₀)/(2*(2-β₀)),4032,div_pos (by linarith) (by linarith),?_⟩
    intro q hq χ hχprim hχ hχ2 hqbig
    apply quadratic_residue_lower_of_no_root hχ hχ2 hβ₀ hβ₀1
      (by dsimp [β₀]; linarith) hqbig
    intro x hx hz
    apply hex
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q => exact ⟨q,χ,hχprim,hχ,hχ2,x,hx,hz⟩

lemma finite_positive_lower {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i∈S,0<f i) : ∃ c : ℝ, 0<c ∧ ∀ i∈S,c≤f i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,zero_lt_one,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨c,hc,hcb⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine ⟨min c (f a),lt_min hc (hf a (Finset.mem_insert_self _ _)),?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hcb i hi)

lemma LFunction_one_finite_lower (N : ℕ) :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      q≤N → χ≠1 → c≤‖χ.LFunction 1‖ := by
  classical
  induction N with
  | zero => exact ⟨1,zero_lt_one,fun q _ χ hq _ => (NeZero.ne q (Nat.eq_zero_of_le_zero hq)).elim⟩
  | succ N ih =>
    obtain ⟨c,hc,hcb⟩ := ih
    obtain ⟨d,hd,hdb⟩ := finite_positive_lower
      ((Finset.univ : Finset (DirichletCharacter ℂ (N+1))).filter (·≠1))
      (fun χ => ‖χ.LFunction 1‖) (fun χ hχ =>
        norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero (Finset.mem_filter.mp hχ).2))
    refine ⟨min c d,lt_min hc hd,?_⟩
    intro q _ χ hq hχ
    rcases Nat.le_succ_iff_eq_or_le.mp hq with rfl|hq
    · exact (min_le_right _ _).trans (hdb χ (by simp [hχ]))
    · exact (min_le_left _ _).trans (hcb q χ hq hχ)

theorem quadratic_siegel {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → χ^2=1 → c*((q:ℝ)+1)^(-ε)≤‖χ.LFunction 1‖ := by
  obtain ⟨c,Q₀,hc,hcb⟩ := quadratic_siegel_eventual hε hε1
  obtain ⟨d,hd,hdb⟩ := LFunction_one_finite_lower ⌈Q₀⌉₊
  refine ⟨min c d,lt_min hc hd,?_⟩
  intro q _ χ hχp hχ hχ2
  by_cases hq : Q₀≤(q:ℝ)+1
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (by positivity) _)).trans
      (hcb q χ hχp hχ hχ2 hq)
  · have hqn : q≤⌈Q₀⌉₊ := by
      have := Nat.le_ceil Q₀
      have : (q:ℝ)≤(⌈Q₀⌉₊:ℝ) := by linarith
      exact_mod_cast this
    have hp : ((q:ℝ)+1)^(-ε)≤1 := Real.rpow_le_one_of_one_le_of_nonpos (by have := Nat.cast_nonneg (α:=ℝ) q; linarith) (by linarith)
    exact (mul_le_of_le_one_right (le_of_lt (lt_min hc hd)) hp).trans
      ((min_le_right _ _).trans (hdb q χ hqn hχ))

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_SiegelBounds

section File_OpenAIPrimeGaps_ZeroFreeBounds

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

section

open Complex Filter Topology Set MeasureTheory Finset

lemma periodic_sum_norm_le_mul {f : ℕ → ℂ} {q : ℕ} {D : ℝ} (hq : 0<q) (hD : 0≤D)
    (hp : ∀ n,f (q+n)=f n) (hz : ∑ n∈range q,f n=0)
    (hb : ∀ n,‖f n‖≤D) (N : ℕ) : ‖∑ n∈range N,f n‖≤q*D := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hN : N<q
    · calc
        _ ≤ ∑ n∈range N,‖f n‖ := norm_sum_le _ _
        _ ≤ ∑ _n∈range N,D := sum_le_sum (fun n _ => hb n)
        _ = N*D := by simp
        _ ≤ q*D := mul_le_mul_of_nonneg_right (by exact_mod_cast hN.le) hD
    · have he : q+(N-q)=N := Nat.add_sub_of_le (not_lt.mp hN)
      rw [←he,sum_range_add,hz,zero_add]
      simp_rw [hp]
      exact ih _ (Nat.sub_lt (lt_of_lt_of_le hq (not_lt.mp hN)) hq)

noncomputable def characterMean {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  (∑ n∈range q,χ (n : ZMod q))/(q:ℂ)

lemma characterMean_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖characterMean χ‖≤1 := by
  rw [characterMean,norm_div,Complex.norm_natCast]
  apply (div_le_one (by exact_mod_cast NeZero.pos q : (0:ℝ)<q)).mpr
  calc
    _ ≤ ∑ n∈range q,‖χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n∈range q,(1:ℝ) := sum_le_sum (fun n _ => χ.norm_le_one _)
    _ = q := by simp

lemma characterMean_eq_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ≠1) :
    characterMean χ=0 := by simp [characterMean,char_sum_range_zero hχ]

lemma discrepancy_characterMean_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {t : ℝ} (ht : 1≤t) :
    ‖seriesDiscrepancy (positiveCoefficients (fun n => χ (n : ZMod q))) (characterMean χ) t‖≤2*q+3 := by
  let c := characterMean χ
  have hc : ‖c‖≤1 := characterMean_norm_le χ
  have hb (n : ℕ) : ‖χ (n : ZMod q)-c‖≤2 := (norm_sub_le _ _).trans (by linarith [χ.norm_le_one (n : ZMod q)])
  have hz : ∑ n∈range q,(χ (n : ZMod q)-c)=0 := by
    rw [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul]
    dsimp [c,characterMean]
    have hq : (q:ℂ)≠0 := by exact_mod_cast NeZero.ne q
    field_simp
    ring
  have hr := periodic_sum_norm_le_mul (NeZero.pos q) (by norm_num : (0:ℝ)≤2)
    (f:=fun n => χ (n : ZMod q)-c) (by intro n; simp) hz hb (⌊t⌋₊+1)
  have he : ∑ n∈range (⌊t⌋₊+1),(χ (n : ZMod q)-c) =
      χ (0 : ZMod q)-c+ ∑ n∈Icc 1 ⌊t⌋₊,(χ (n : ZMod q)-c) := by
    rw [Nat.range_succ_eq_Icc_zero,←Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le ⌊t⌋₊)]
    simp
    ring
  have ht0 : 0≤t := by linarith
  have hfloor : ‖(⌊t⌋₊:ℂ)-(t:ℂ)‖≤1 := by
    rw [←Complex.ofReal_natCast,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le ht0))]
    have := Nat.lt_floor_add_one t
    linarith
  have heq : seriesDiscrepancy (positiveCoefficients (fun n => χ (n : ZMod q))) c t =
      (∑ n∈range (⌊t⌋₊+1),(χ (n : ZMod q)-c))-(χ 0-c)+c*((⌊t⌋₊:ℂ)-(t:ℂ)) := by
    rw [he]
    simp only [seriesDiscrepancy,sum_positiveCoefficients,sum_sub_distrib,sum_const,Nat.card_Icc,
      Nat.add_sub_cancel,nsmul_eq_mul]
    ring
  rw [heq]
  calc
    _ ≤ ‖∑ n∈range (⌊t⌋₊+1),(χ (n : ZMod q)-c)‖+‖χ 0-c‖+‖c*((⌊t⌋₊:ℂ)-(t:ℂ))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (q:ℝ)*2+2+1 := by
      gcongr
      · simpa using hb 0
      · rw [norm_mul]; exact (mul_le_mul hc hfloor (norm_nonneg _) zero_le_one).trans_eq (by ring)
    _ = _ := by ring

lemma LFunction_regularSeries_characterMean {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    χ.LFunction s = regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) (characterMean χ) s+
      characterMean χ/(s-1) := by
  rw [regularSeries_eq_LSeries_sub (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
    (by positivity : (0:ℝ)≤2*q+3) (fun t ht => discrepancy_characterMean_bound χ ht.le) hs,
    sub_add_cancel,LSeries_positiveCoefficients,←χ.LFunction_eq_LSeries hs]

lemma LFunction_deriv_norm_small_power {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1/2) :
    ∃ K : ℝ,0<K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),χ≠1 →
      ∀ s : ℂ,1-ε/2 ≤ s.re → ‖deriv χ.LFunction s‖≤K*((q+2)*(‖s‖+2))^(2*ε) := by
  obtain ⟨K,hK,h⟩ := regularSeries_deriv_norm_small_power hε hε1
  refine ⟨K,hK,?_⟩
  intro q _ χ hχ s hs
  have he : regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) 0 =ᶠ[𝓝 s] χ.LFunction := by
    filter_upwards [(continuous_re.tendsto s).eventually (lt_mem_nhds (by linarith : 0<s.re))] with z hz
    exact regularSeries_character_eq hχ hz
  rw [←he.deriv_eq]
  have hb := h _ 0 (q+1) (positiveCoefficients_zero _) (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
    (by simp) (by positivity) (fun t _ => discrepancy_character_bound hχ t) s hs
  convert hb using 1
  congr 3
  ring

noncomputable def characterRegular {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) (characterMean χ)

lemma character_line_bounds {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1/2) :
    ∃ K : ℝ,1≤K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ),
      (∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
        ‖characterRegular χ s‖≤K*((q+2)*(|t|+2))^(2*ε)) ∧
      (χ≠1 → ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
        ‖deriv χ.LFunction s‖≤K*((q+2)*(|t|+2))^(2*ε)) := by
  obtain ⟨K₀,hK₀,h₀⟩ := regularSeries_norm_small_power hε hε1
  obtain ⟨K₁,hK₁,h₁⟩ := LFunction_deriv_norm_small_power hε hε1
  let K := 1+K₀*8^(2*ε)+K₁*4^(2*ε)
  have hp₀ : 0≤K₀*8^(2*ε) := by positivity
  have hp₁ : 0≤K₁*4^(2*ε) := by positivity
  have hK : 1≤K := by dsimp [K]; linarith
  refine ⟨K,hK,?_⟩
  intro q _ χ t
  have hq : (0:ℝ)≤q := Nat.cast_nonneg q
  have ht : 0≤|t| := abs_nonneg t
  have hp : 0≤((q:ℝ)+2)*(|t|+2) := by positivity
  have he : 0≤2*ε := by positivity
  constructor
  · intro s hs hn
    have hb := h₀ _ (characterMean χ) (2*q+3) (positiveCoefficients_zero _)
      (positiveCoefficients_norm_le (fun n => χ.norm_le_one _)) (characterMean_norm_le χ)
      (by positivity) (fun t ht => discrepancy_characterMean_bound χ ht) s (by linarith)
    change ‖characterRegular χ s‖≤_ at hb
    have hb' : (2*q+3+1)*(‖s‖+2)≤8*(((q:ℝ)+2)*(|t|+2)) := by
      nlinarith [mul_nonneg (show (0:ℝ)≤2*q+4 by positivity) (sub_nonneg.mpr hn)]
    calc
      _ ≤ K₀*((2*q+3+1)*(‖s‖+2))^(2*ε) := hb
      _ ≤ K₀*(8*(((q:ℝ)+2)*(|t|+2)))^(2*ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hb' he) hK₀.le
      _ = (K₀*8^(2*ε))*(((q:ℝ)+2)*(|t|+2))^(2*ε) := by rw [Real.mul_rpow (by norm_num) hp]; ring
      _ ≤ _ := by gcongr; dsimp [K]; linarith
  · intro hχ s hs hn
    have hb := h₁ q χ hχ s (by linarith)
    have hb' : (q+2)*(‖s‖+2)≤4*(((q:ℝ)+2)*(|t|+2)) := by
      nlinarith [mul_nonneg (show (0:ℝ)≤q+2 by positivity) (sub_nonneg.mpr hn)]
    calc
      _ ≤ K₁*((q+2)*(‖s‖+2))^(2*ε) := hb
      _ ≤ K₁*(4*(((q:ℝ)+2)*(|t|+2)))^(2*ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hb' he) hK₁.le
      _ = (K₁*4^(2*ε))*(((q:ℝ)+2)*(|t|+2))^(2*ε) := by rw [Real.mul_rpow (by norm_num) hp]; ring
      _ ≤ _ := by gcongr; dsimp [K]; linarith

lemma line_growth_lipschitz {f : ℂ → ℂ} {t D : ℝ} (hf : Differentiable ℂ f)
    (hb : ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) → ‖deriv f s‖≤D)
    {z w : ℂ} (hz : 1 ≤ z.re) (hw : 1 ≤ w.re)
    (hzn : ‖z‖+2≤4*(|t|+2)) (hwn : ‖w‖+2≤4*(|t|+2)) :
    ‖f z-f w‖≤D*‖z-w‖ := by
  let S := {s : ℂ | 1 ≤ s.re} ∩ Metric.closedBall 0 (4*(|t|+2)-2)
  have hS : Convex ℝ S := (convex_halfSpace_re_ge 1).inter (convex_closedBall 0 _)
  apply Convex.norm_image_sub_le_of_norm_deriv_le (s:=S) (fun z _ => hf z) ?_ hS
      ⟨hw,by simp [Metric.mem_closedBall,dist_zero_right]; linarith⟩
      ⟨hz,by simp [Metric.mem_closedBall,dist_zero_right]; linarith⟩
  intro s hs
  exact hb s hs.1 (by have := hs.2; simp only [Metric.mem_closedBall,dist_zero_right] at this; linarith)

end

lemma three_four_one_lower {a D E : ℝ} (ha : 0≤a) (hD : 1≤D) (hE : 1≤E)
    (h : ∀ δ : ℝ,0<δ → δ≤1 → 1≤(2*D/δ)^3*(a+D*δ)^4*E) :
    1/(256*D^6*E)≤a := by
  have hD0 : 0<D := by linarith
  have hE0 : 0<E := by linarith
  let δ := 1/(256*D^7*E)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδ1 : δ≤1 := by
    have hp : (1:ℝ)≤D^7 := one_le_pow₀ hD
    have hp' : (1:ℝ)≤D^7*E := one_le_mul_of_one_le_of_one_le hp hE
    dsimp [δ]
    apply (div_le_one (by positivity)).mpr
    linarith
  have he : 1/(256*D^6*E)=D*δ := by dsimp [δ]; field_simp
  rw [he]
  by_contra! han
  have hb : a+D*δ≤2*D*δ := by linarith
  have hh := h δ hδ hδ1
  have hu : (2*D/δ)^3*(a+D*δ)^4*E≤(2*D/δ)^3*(2*D*δ)^4*E := by gcongr
  have hv : (2*D/δ)^3*(2*D*δ)^4*E=1/2 := by dsimp [δ]; field_simp; norm_num
  rw [hv] at hu
  linarith

open Complex Filter Topology Finset

lemma line_sample_norm {δ t u : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1) (hu : |u|≤2*|t|) :
    ‖(1:ℂ)+δ+I*u‖+2≤4*(|t|+2) := by
  have h := Complex.norm_le_abs_re_add_abs_im ((1:ℂ)+δ+I*u)
  simp only [Complex.add_re,Complex.one_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
    Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_self,add_zero,Complex.add_im,
    Complex.one_im,Complex.mul_im,one_mul,zero_add] at h
  rw [abs_of_nonneg (by linarith : (0:ℝ)≤1+δ)] at h
  linarith [abs_nonneg t]

lemma LFunction_norm_le_regular_add_pole {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    ‖χ.LFunction s‖≤‖characterRegular χ s‖+1/‖s-1‖ := by
  rw [LFunction_regularSeries_characterMean χ hs]
  apply (norm_add_le _ _).trans
  dsimp [characterRegular]
  apply add_le_add le_rfl
  rw [norm_div]
  exact div_le_div_of_nonneg_right (characterMean_norm_le χ) (norm_nonneg _)

lemma characterRegular_eq_nonprincipal {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {s : ℂ} (hs : 0<s.re) : characterRegular χ s=χ.LFunction s := by
  rw [characterRegular,characterMean_eq_zero hχ,regularSeries_character_eq hχ hs]

lemma nonprincipal_line_lower_aux {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {t c K P : ℝ} (hc : 0<c) (_hc1 : c≤1) (hK : 1≤K) (hP : 1≤P)
    (hr : ∀ ψ : DirichletCharacter ℂ q,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P)
    (hd : ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) → ‖deriv χ.LFunction s‖≤K*P)
    (hsi : χ^2=1 → c/P≤‖χ.LFunction 1‖) :
    min (c/2) (1/(256*K^6*(K+K/c)))/P^8≤‖χ.LFunction (1+I*t)‖ := by
  have hK0 : 0<K := by linarith
  have hP0 : 0<P := by linarith
  have hhc : 0<K+K/c := by positivity
  have hKP : 1≤K*P := one_le_mul_of_one_le_of_one_le hK hP
  have hn0 : ‖(1:ℂ)+I*t‖+2≤4*(|t|+2) := by
    simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
  have hn1 : ‖(1:ℂ)‖+2≤4*(|t|+2) := by norm_num; linarith [abs_nonneg t]
  by_cases hsmall : χ^2=1 ∧ |t|≤c/(2*K*P^2)
  · have hdiff := line_growth_lipschitz (DirichletCharacter.differentiable_LFunction hχ) hd
      (z:=1) (w:=1+I*t) (by simp) (by simp) hn1 hn0
    have hnorm : ‖(1:ℂ)-(1+I*t)‖=|t| := by
      rw [show (1:ℂ)-(1+I*t)=-(I*t) by ring,norm_neg,norm_mul,Complex.norm_I,one_mul,
        Complex.norm_real,Real.norm_eq_abs]
    rw [hnorm] at hdiff
    have hdiff' : ‖χ.LFunction 1-χ.LFunction (1+I*t)‖≤c/(2*P) := by
      calc
        _ ≤ K*P*|t| := hdiff
        _ ≤ K*P*(c/(2*K*P^2)) := mul_le_mul_of_nonneg_left hsmall.2 (by positivity)
        _ = _ := by field_simp
    have hval : c/(2*P)≤‖χ.LFunction (1+I*t)‖ := by
      have htri := norm_add_le (χ.LFunction 1-χ.LFunction (1+I*t)) (χ.LFunction (1+I*t))
      rw [sub_add_cancel] at htri
      have he : c/P=2*(c/(2*P)) := by ring
      have hsi' := hsi hsmall.1
      rw [he] at hsi'
      linarith
    have hP8 : P≤P^8 := by simpa using pow_le_pow_right₀ hP (show (1:ℕ)≤8 by norm_num)
    calc
      _ ≤ (c/2)/P^8 := div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
      _ ≤ (c/2)/P := div_le_div_of_nonneg_left (by positivity) hP0 hP8
      _ = c/(2*P) := by ring
      _ ≤ _ := hval
  · have hLo : 1/(256*(K*P)^6*((K+K/c)*P^2))≤‖χ.LFunction (1+I*t)‖ := by
      apply three_four_one_lower (norm_nonneg _) hKP
        (one_le_mul_of_one_le_of_one_le (by linarith [div_pos hK0 hc]) (one_le_pow₀ hP))
      intro δ hδ hδ1
      have hrδ : ((1:ℂ)+δ+I*t).re=1+δ := by simp
      have hrδ2 : ((1:ℂ)+δ+2*I*t).re=1+δ := by simp
      have hnδ := line_sample_norm hδ.le hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
      have hnδ2 : ‖(1:ℂ)+δ+2*I*t‖+2≤4*(|t|+2) := by
        simpa only [show I*((2*t:ℝ):ℂ)=2*I*t by push_cast; ring] using
          line_sample_norm hδ.le hδ1 (t:=t) (u:=2*t) (by rw [abs_mul]; norm_num)
      have hL0 : ‖DirichletCharacter.LFunctionTrivChar q (1+δ)‖≤2*(K*P)/δ := by
        have hn : ‖(1:ℂ)+δ‖+2≤4*(|t|+2) := by
          simpa using line_sample_norm hδ.le hδ1 (t:=t) (u:=0) (by simp)
        have hreg := hr (1:DirichletCharacter ℂ q) (1+δ) (by simp; linarith) hn
        have hp := LFunction_norm_le_regular_add_pole (1:DirichletCharacter ℂ q)
          (s:=1+δ) (by simp; linarith)
        have hden : ‖(1:ℂ)+δ-1‖=δ := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
        rw [hden] at hp
        change ‖DirichletCharacter.LFunction (1:DirichletCharacter ℂ q) (1+δ)‖≤_
        apply (hp.trans (add_le_add hreg le_rfl)).trans
        apply (le_div_iff₀ hδ).mpr
        have hd : (K*P)*δ≤K*P := mul_le_of_le_one_right (by positivity) hδ1
        field_simp
        nlinarith
      have hLχ : ‖χ.LFunction (1+δ+I*t)‖≤‖χ.LFunction (1+I*t)‖+(K*P)*δ := by
        have hl := line_growth_lipschitz (DirichletCharacter.differentiable_LFunction hχ) hd
          (z:=1+δ+I*t) (w:=1+I*t) (by simp; linarith) (by simp) hnδ hn0
        have hden : ‖(1:ℂ)+δ+I*t-(1+I*t)‖=δ := by
          rw [show (1:ℂ)+δ+I*t-(1+I*t)=(δ:ℂ) by ring,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
        rw [hden] at hl
        have ht := norm_add_le (χ.LFunction (1+δ+I*t)-χ.LFunction (1+I*t)) (χ.LFunction (1+I*t))
        rw [sub_add_cancel] at ht
        linarith
      have hL2 : ‖(χ^2).LFunction (1+δ+2*I*t)‖≤(K+K/c)*P^2 := by
        by_cases hχ2 : χ^2=1
        · have ht : c/(2*K*P^2)< |t| := lt_of_not_ge (fun ht => hsmall ⟨hχ2,ht⟩)
          have ht0 : 0< |t| := (by positivity : 0<c/(2*K*P^2)).trans ht
          have hp := LFunction_norm_le_regular_add_pole (χ^2) (s:=1+δ+2*I*t) (by rw [hrδ2]; linarith)
          have hn : 2*|t|≤‖(1:ℂ)+δ+2*I*t-1‖ := by
            have h := Complex.abs_im_le_norm ((1:ℂ)+δ+2*I*t-1)
            simpa [abs_mul] using h
          have hfrac : 1/‖(1:ℂ)+δ+2*I*t-1‖≤K*P^2/c := by
            apply (div_le_div_of_nonneg_left zero_le_one (by positivity : 0<2*|t|) hn).trans
            apply (div_le_iff₀ (by positivity : 0<2*|t|)).mpr
            have ht' := (div_lt_iff₀ (by positivity : 0<2*K*P^2)).mp ht
            rw [div_mul_eq_mul_div]
            apply (le_div_iff₀ hc).mpr
            nlinarith
          have hreg := hr (χ^2) (1+δ+2*I*t) (by rw [hrδ2]; linarith) hnδ2
          have hP2 : P≤P^2 := by nlinarith
          have h := hp.trans (add_le_add hreg hfrac)
          apply h.trans
          calc
            K*P+K*P^2/c ≤ K*P^2+K*P^2/c := add_le_add (mul_le_mul_of_nonneg_left hP2 hK0.le) le_rfl
            _ = _ := by ring
        · have hreg := hr (χ^2) (1+δ+2*I*t) (by rw [hrδ2]; linarith) hnδ2
          rw [characterRegular_eq_nonprincipal hχ2 (by rw [hrδ2]; linarith)] at hreg
          have hP2 : P≤P^2 := by nlinarith
          exact hreg.trans (by nlinarith [mul_le_mul_of_nonneg_left hP2 hK0.le,div_pos hK0 hc])
      have hprod := χ.norm_LFunction_product_ge_one hδ t
      simp only [norm_mul,norm_pow] at hprod
      exact hprod.trans (by gcongr)
    calc
      _ ≤ (1/(256*K^6*(K+K/c)))/P^8 := div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = 1/(256*(K*P)^6*((K+K/c)*P^2)) := by field_simp
      _ ≤ _ := hLo

lemma nonprincipal_line_lower {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ,0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → ∀ t : ℝ,
        c*(((q:ℝ)+2)*(|t|+2))^(-ε)≤‖χ.LFunction (1+I*t)‖ := by
  obtain ⟨K,hK,hgrowth⟩ := character_line_bounds (by linarith : 0<ε/16) (by linarith : ε/16≤1/2)
  obtain ⟨c₀,hc₀,hsiegel⟩ := quadratic_siegel (by linarith : 0<ε/8) (by linarith : ε/8≤1)
  let c := min c₀ 1
  have hc : 0<c := lt_min hc₀ zero_lt_one
  have hc1 : c≤1 := min_le_right _ _
  let d := min (c/2) (1/(256*K^6*(K+K/c)))
  have hK0 : 0<K := by linarith
  have hd : 0<d := by dsimp [d]; positivity
  refine ⟨d,hd,?_⟩
  intro q _ χ hχp hχ t
  let X : ℝ := ((q:ℝ)+2)*(|t|+2)
  let P : ℝ := X^(ε/8)
  have hX : 1≤X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
  have hX0 : 0<X := by linarith
  have hP : 1≤P := Real.one_le_rpow hX (by positivity)
  have he : 2*(ε/16)=ε/8 := by ring
  have hsi : χ^2=1 → c/P≤‖χ.LFunction 1‖ := by
    intro hχ2
    have hq : (q:ℝ)+1≤X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
    calc
      c/P = c*X^(-(ε/8)) := by rw [Real.rpow_neg hX0.le]; rfl
      _ ≤ c₀*((q:ℝ)+1)^(-(ε/8)) := by
        apply mul_le_mul (min_le_left _ _) (Real.rpow_le_rpow_of_nonpos (by positivity) hq (by linarith))
          (Real.rpow_nonneg hX0.le _) hc₀.le
      _ ≤ _ := hsiegel q χ hχp hχ hχ2
  have hh := nonprincipal_line_lower_aux hχ hc hc1 hK hP
    (fun ψ s hs hn => by simpa only [he] using (hgrowth q ψ t).1 s hs hn)
    (fun s hs hn => by simpa only [he] using (hgrowth q χ t).2 hχ s hs hn) hsi
  have hP8 : P^8=X^ε := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast hX0.le]
    congr 1
    norm_num
  change d/P^8≤_ at hh
  rw [hP8] at hh
  change d*X^(-ε)≤_
  simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hh

lemma character_interior_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {t K P δ : ℝ} (hK : 1≤K) (hP : 1≤P) (hδ : 0<δ) (hδ1 : δ≤1)
    (hr : ∀ ψ : DirichletCharacter ℂ q,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P) :
    δ/(2*K*P)≤‖χ.LFunction (1+δ+I*t)‖ := by
  have hKP : 1≤K*P := one_le_mul_of_one_le_of_one_le hK hP
  have hKP0 : 0<K*P := by linarith
  have hb (ψ : DirichletCharacter ℂ q) (u : ℝ) (hu : |u|≤2*|t|) :
      ‖ψ.LFunction (1+δ+I*u)‖≤2*K*P/δ := by
    have hp := LFunction_norm_le_regular_add_pole ψ (s:=1+δ+I*u) (by simp; linarith)
    have hn : δ≤‖(1:ℂ)+δ+I*u-1‖ := by
      simpa using Complex.re_le_norm ((1:ℂ)+δ+I*u-1)
    have hreg := hr ψ (1+δ+I*u) (by simp; linarith) (line_sample_norm hδ.le hδ1 hu)
    have hfrac := div_le_div_of_nonneg_left zero_le_one hδ hn
    apply (hp.trans (add_le_add hreg hfrac)).trans
    apply (le_div_iff₀ hδ).mpr
    have hd := mul_le_of_le_one_right hKP0.le hδ1
    have he : (K*P+1/δ)*δ=K*P*δ+1 := by field_simp
    rw [he]
    nlinarith
  have h0 : ‖DirichletCharacter.LFunctionTrivChar q (1+δ)‖≤2*K*P/δ := by
    simpa using hb (1:DirichletCharacter ℂ q) 0 (by simp)
  have h2 : ‖(χ^2).LFunction (1+δ+2*I*t)‖≤2*K*P/δ := by
    simpa only [show I*((2*t:ℝ):ℂ)=2*I*t by push_cast; ring] using hb (χ^2) (2*t) (by rw [abs_mul]; norm_num)
  have hh := χ.norm_LFunction_product_ge_one hδ t
  simp only [norm_mul,norm_pow] at hh
  have hu : 1≤(2*K*P/δ)^3*‖χ.LFunction (1+δ+I*t)‖^4*(2*K*P/δ) := hh.trans (by gcongr)
  have hp : (1:ℝ)^4≤((2*K*P/δ)*‖χ.LFunction (1+δ+I*t)‖)^4 := by convert hu using 1 <;> ring
  have hv := le_of_pow_le_pow_left₀ (by norm_num : (4:ℕ)≠0) (by positivity) hp
  apply (div_le_iff₀ (by positivity : 0<2*K*P)).mpr
  have he : (2*K*P/δ)*‖χ.LFunction (1+δ+I*t)‖=(‖χ.LFunction (1+δ+I*t)‖*(2*K*P))/δ := by ring
  rw [he] at hv
  simpa only [one_mul] using (le_div_iff₀ hδ).mp hv

lemma nonprincipal_strip_lower_aux {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {t c K P δ : ℝ} (hc : 0<c) (hK : 1≤K) (hP : 1≤P)
    (hδ : 0≤δ) (hδ1 : δ≤1)
    (hr : ∀ ψ : DirichletCharacter ℂ q,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P)
    (hd : ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) → ‖deriv χ.LFunction s‖≤K*P)
    (hl : c/P≤‖χ.LFunction (1+I*t)‖) :
    (c/(4*K^2))/P^3≤‖χ.LFunction (1+δ+I*t)‖ := by
  have hK0 : 0<K := by linarith
  have hP0 : 0<P := by linarith
  by_cases hnear : δ≤c/(2*K*P^2)
  · have hn0 : ‖(1:ℂ)+I*t‖+2≤4*(|t|+2) := by
      simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
    have hnδ := line_sample_norm hδ hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
    have hdif := line_growth_lipschitz (DirichletCharacter.differentiable_LFunction hχ) hd
      (z:=1+I*t) (w:=1+δ+I*t) (by simp) (by simp; linarith) hn0 hnδ
    have hnorm : ‖(1:ℂ)+I*t-(1+δ+I*t)‖=δ := by
      rw [show (1:ℂ)+I*t-(1+δ+I*t)=-(δ:ℂ) by ring,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hδ]
    rw [hnorm] at hdif
    have hdb : ‖χ.LFunction (1+I*t)-χ.LFunction (1+δ+I*t)‖≤c/(2*P) := by
      apply hdif.trans
      calc
        K*P*δ ≤ K*P*(c/(2*K*P^2)) := mul_le_mul_of_nonneg_left hnear (by positivity)
        _ = _ := by field_simp
    have htri := norm_add_le (χ.LFunction (1+I*t)-χ.LFunction (1+δ+I*t)) (χ.LFunction (1+δ+I*t))
    rw [sub_add_cancel] at htri
    have hva : c/(2*P)≤‖χ.LFunction (1+δ+I*t)‖ := by
      have he : c/P=2*(c/(2*P)) := by ring
      rw [he] at hl
      linarith
    apply le_trans ?_ hva
    rw [div_div]
    apply div_le_div_of_nonneg_left hc.le (by positivity)
    have hP3 : P≤P^3 := by simpa using pow_le_pow_right₀ hP (show (1:ℕ)≤3 by norm_num)
    have hK2 : 1≤K^2 := one_le_pow₀ hK
    nlinarith [mul_le_mul_of_nonneg_left hP3 (show (0:ℝ)≤4*K^2 by positivity)]
  · have hδ0 : 0<δ := (by positivity : 0<c/(2*K*P^2)).trans (lt_of_not_ge hnear)
    apply le_trans ?_ (character_interior_lower χ hK hP hδ0 hδ1 hr)
    calc
      (c/(4*K^2))/P^3 = (c/(2*K*P^2))/(2*K*P) := by field_simp; norm_num
      _ ≤ δ/(2*K*P) := div_le_div_of_nonneg_right (le_of_not_ge hnear) (by positivity)

lemma nonprincipal_strip_lower {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ,0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → ∀ σ t : ℝ, 1≤σ → σ≤2 →
        c*(((q:ℝ)+2)*(|t|+2))^(-ε)≤‖χ.LFunction (σ+I*t)‖ := by
  obtain ⟨K,hK,hg⟩ := character_line_bounds (by linarith : 0<ε/6) (by linarith : ε/6≤1/2)
  obtain ⟨c,hc,hl⟩ := nonprincipal_line_lower (by linarith : 0<ε/3) (by linarith : ε/3≤1)
  have hK0 : 0<K := by linarith
  refine ⟨c/(4*K^2),by positivity,?_⟩
  intro q _ χ hχp hχ σ t hσ hσ2
  let X : ℝ := ((q:ℝ)+2)*(|t|+2)
  let P : ℝ := X^(ε/3)
  have hX : 1≤X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
  have hX0 : 0<X := by linarith
  have hP : 1≤P := Real.one_le_rpow hX (by positivity)
  have he : 2*(ε/6)=ε/3 := by ring
  have hl' : c/P≤‖χ.LFunction (1+I*t)‖ := by
    have hh := hl q χ hχp hχ t
    change c*X^(-(ε/3))≤_ at hh
    change c/X^(ε/3)≤_
    simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hh
  have hb := nonprincipal_strip_lower_aux hχ hc hK hP (δ:=σ-1) (by linarith) (by linarith)
    (fun ψ s hs hn => by simpa only [he] using (hg q ψ t).1 s hs hn)
    (fun s hs hn => by simpa only [he] using (hg q χ t).2 hχ s hs hn) hl'
  have hP3 : P^3=X^ε := by dsimp [P]; rw [←Real.rpow_mul_natCast hX0.le]; congr 1; norm_num
  rw [hP3] at hb
  have hs : (1:ℂ)+((σ-1:ℝ):ℂ)+I*t=(σ:ℂ)+I*t := by push_cast; ring
  rw [hs] at hb
  change (c/(4*K^2))*X^(-ε)≤_
  simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hb

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_ZeroFreeBounds

section File_OpenAIPrimeGaps_PrincipalGrowth

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Complex Filter Topology

lemma zetaRegular_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ s : ℂ, 1-ε/2 ≤ s.re →
      ‖zetaRegular s‖ ≤ K*(‖s‖+2)^(2*ε) ∧
      ‖deriv zetaRegular s‖ ≤ K*(‖s‖+2)^(2*ε) := by
  obtain ⟨K₀,hK₀,h₀⟩ := regularSeries_norm_small_power hε hε1
  obtain ⟨K₁,hK₁,h₁⟩ := regularSeries_deriv_norm_small_power hε hε1
  let K := 1+(K₀+K₁)*2^(2*ε)
  have hK : 1 ≤ K := by dsimp [K]; linarith [show 0 < (K₀+K₁)*2^(2*ε) by positivity]
  refine ⟨K,hK,?_⟩
  intro s hs
  have hb₀ := h₀ _ 1 1 (positiveCoefficients_zero _) (positiveCoefficients_norm_le (by simp))
    (by simp) zero_le_one (fun t ht => discrepancy_constant_bound ht) s (by linarith)
  have hb₁ := h₁ _ 1 1 (positiveCoefficients_zero _) (positiveCoefficients_norm_le (by simp))
    (by simp) zero_le_one (fun t ht => discrepancy_constant_bound ht) s hs
  change ‖zetaRegular s‖ ≤ _ at hb₀
  change ‖deriv zetaRegular s‖ ≤ _ at hb₁
  norm_num only [one_add_one_eq_two] at hb₀ hb₁
  rw [Real.mul_rpow (by norm_num) (by positivity)] at hb₀ hb₁
  constructor
  · apply hb₀.trans
    have hc : K₀*2^(2*ε) ≤ K := by dsimp [K]; nlinarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (2*ε)]
    calc
      _ = (K₀*2^(2*ε))*(‖s‖+2)^(2*ε) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
  · apply hb₁.trans
    have hc : K₁*2^(2*ε) ≤ K := by dsimp [K]; nlinarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (2*ε)]
    calc
      _ = (K₁*2^(2*ε))*(‖s‖+2)^(2*ε) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

lemma zeta_deriv_eq_regular {s : ℂ} (hs : 0 < s.re) (hs1 : s≠1) :
    deriv riemannZeta s = deriv zetaRegular s-1/(s-1)^2 := by
  have he : riemannZeta =ᶠ[𝓝 s] fun z => zetaRegular z+1/(z-1) := by
    filter_upwards [(continuous_re.tendsto s).eventually (lt_mem_nhds hs),
      eventually_ne_nhds hs1] with z hz hz1
    rw [zetaRegular_eq hz hz1,sub_add_cancel]
  rw [he.deriv_eq]
  have hd := (hasDerivAt_const s (1:ℂ)).div ((hasDerivAt_id s).sub_const 1) (sub_ne_zero.mpr hs1)
  have hh := (zetaRegular_differentiableAt hs).hasDerivAt.add hd
  simpa only [Pi.add_def, Pi.div_def, id_eq, zero_mul, one_mul, zero_sub, neg_div, sub_eq_add_neg, zero_add] using hh.deriv

lemma horizontal_growth_lipschitz {f : ℂ → ℂ} {t D : ℝ}
    (hf : ∀ s : ℂ, 1 ≤ s.re → s.im=t → DifferentiableAt ℂ f s)
    (hb : ∀ s : ℂ, 1 ≤ s.re → s.im=t → ‖s‖+2 ≤ 4*(|t|+2) → ‖deriv f s‖ ≤ D)
    {z w : ℂ} (hz : 1 ≤ z.re) (hw : 1 ≤ w.re) (hzt : z.im=t) (hwt : w.im=t)
    (hzn : ‖z‖+2 ≤ 4*(|t|+2)) (hwn : ‖w‖+2 ≤ 4*(|t|+2)) :
    ‖f z-f w‖ ≤ D*‖z-w‖ := by
  let S := ({s : ℂ | 1 ≤ s.re} ∩ {s : ℂ | s.im=t}) ∩ Metric.closedBall 0 (4*(|t|+2)-2)
  have hi : Convex ℝ {s : ℂ | s.im=t} := convex_hyperplane (.mk Complex.add_im Complex.smul_im) t
  have hS : Convex ℝ S := ((convex_halfSpace_re_ge 1).inter hi).inter (convex_closedBall 0 _)
  apply Convex.norm_image_sub_le_of_norm_deriv_le (s:=S) (fun z hz => hf z hz.1.1 hz.1.2) ?_ hS
    ⟨⟨hw,hwt⟩,by simp [Metric.mem_closedBall,dist_zero_right]; linarith⟩
    ⟨⟨hz,hzt⟩,by simp [Metric.mem_closedBall,dist_zero_right]; linarith⟩
  intro s hs
  exact hb s hs.1.1 hs.1.2 (by have := hs.2; simp only [Metric.mem_closedBall,dist_zero_right] at this; linarith)

lemma zeta_high_line_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ t : ℝ, 1 ≤ |t| →
      (∀ ψ : DirichletCharacter ℂ 1, ∀ s : ℂ, 1 ≤ s.re → ‖s‖+2 ≤ 4*(|t|+2) →
        ‖characterRegular ψ s‖ ≤ K*(|t|+2)^(2*ε)) ∧
      (∀ s : ℂ, 1 ≤ s.re → s.im=t → ‖s‖+2 ≤ 4*(|t|+2) →
        ‖deriv riemannZeta s‖ ≤ K*(|t|+2)^(2*ε)) := by
  obtain ⟨K₀,hK₀,h₀⟩ := character_line_bounds hε hε1
  obtain ⟨K₁,hK₁,h₁⟩ := zetaRegular_bounds hε hε1
  let K := K₀*3^(2*ε)+K₁*4^(2*ε)+1
  have hK₀' : 0 < K₀ := by linarith
  have hK₁' : 0 < K₁ := by linarith
  have hK : 1 ≤ K := by dsimp [K]; linarith [show 0 < K₀*3^(2*ε) by positivity, show 0 < K₁*4^(2*ε) by positivity]
  refine ⟨K,hK,?_⟩
  intro t ht
  have hP : 1 ≤ (|t|+2)^(2*ε) := Real.one_le_rpow (by linarith [abs_nonneg t]) (by positivity)
  constructor
  · intro ψ s hs hn
    have hb := (h₀ 1 ψ t).1 s hs hn
    norm_num only [Nat.cast_one,show (1:ℝ)+2=3 by norm_num] at hb
    rw [Real.mul_rpow (by norm_num) (by positivity)] at hb
    apply hb.trans
    have hc : K₀*3^(2*ε) ≤ K := by dsimp [K]; linarith [show 0 < K₁*4^(2*ε) by positivity]
    convert mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (|t|+2)^(2*ε)) using 1
    ring
  · intro s hs him hn
    have hs1 : s≠1 := by intro h; simp [h] at him; rw [←him] at ht; norm_num at ht
    have hd := (h₁ s (by linarith)).2
    have hden : 1 ≤ ‖s-1‖ := by
      have h := Complex.abs_im_le_norm (s-1)
      simp only [Complex.sub_im,Complex.one_im,sub_zero,him] at h
      exact ht.trans h
    have hfrac : ‖(1:ℂ)/(s-1)^2‖ ≤ 1 := by
      simp only [norm_div,norm_one,norm_pow]
      exact div_le_one_of_le₀ (one_le_pow₀ hden) (by positivity)
    rw [zeta_deriv_eq_regular (by linarith) hs1]
    apply (norm_sub_le _ _).trans
    have hnorm := Real.rpow_le_rpow (by positivity : 0 ≤ ‖s‖+2) hn (by positivity : 0 ≤ 2*ε)
    rw [Real.mul_rpow (by norm_num) (by positivity)] at hnorm
    have hc : K₁*4^(2*ε)+1 ≤ K := by dsimp [K]; linarith [show 0 < K₀*3^(2*ε) by positivity]
    calc
      _ ≤ K₁*(‖s‖+2)^(2*ε)+1 := add_le_add hd hfrac
      _ ≤ (K₁*4^(2*ε))*(|t|+2)^(2*ε)+(|t|+2)^(2*ε) := by nlinarith
      _ = (K₁*4^(2*ε)+1)*(|t|+2)^(2*ε) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

lemma zeta_high_line_lower_aux {t K P : ℝ} (ht : 1 ≤ |t|) (hK : 1 ≤ K) (hP : 1 ≤ P)
    (hr : ∀ ψ : DirichletCharacter ℂ 1, ∀ s : ℂ, 1 ≤ s.re → ‖s‖+2 ≤ 4*(|t|+2) →
      ‖characterRegular ψ s‖ ≤ K*P)
    (hd : ∀ s : ℂ, 1 ≤ s.re → s.im=t → ‖s‖+2 ≤ 4*(|t|+2) → ‖deriv riemannZeta s‖ ≤ K*P) :
    (1/(512*K^7))/P^7 ≤ ‖riemannZeta (1+I*t)‖ := by
  have hK0 : 0 < K := by linarith
  have hP0 : 0 < P := by linarith
  have hKP : 1 ≤ K*P := one_le_mul_of_one_le_of_one_le hK hP
  have hh : 1/(256*(K*P)^6*(2*K*P)) ≤ ‖riemannZeta (1+I*t)‖ := by
    apply three_four_one_lower (norm_nonneg _) hKP (by linarith)
    intro δ hδ hδ1
    have hn0 : ‖(1:ℂ)+I*t‖+2 ≤ 4*(|t|+2) := by
      simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
    have hnδ := line_sample_norm hδ.le hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
    have hL0 : ‖DirichletCharacter.LFunctionTrivChar 1 (1+δ)‖ ≤ 2*(K*P)/δ := by
      have hn : ‖(1:ℂ)+δ‖+2 ≤ 4*(|t|+2) := by
        simpa using line_sample_norm hδ.le hδ1 (t:=t) (u:=0) (by simp)
      have hreg := hr 1 (1+δ) (by simp; linarith) hn
      have hp := LFunction_norm_le_regular_add_pole (1:DirichletCharacter ℂ 1)
        (s:=1+δ) (by simp; linarith)
      have hden : ‖(1:ℂ)+δ-1‖=δ := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
      rw [hden] at hp
      change ‖DirichletCharacter.LFunction (1:DirichletCharacter ℂ 1) (1+δ)‖ ≤ _
      apply (hp.trans (add_le_add hreg le_rfl)).trans
      apply (le_div_iff₀ hδ).mpr
      have hd := mul_le_of_le_one_right (by positivity : 0 ≤ K*P) hδ1
      field_simp
      nlinarith
    have hL1 : ‖riemannZeta (1+δ+I*t)‖ ≤ ‖riemannZeta (1+I*t)‖+(K*P)*δ := by
      have hf (s : ℂ) (_hs : 1 ≤ s.re) (him : s.im=t) : DifferentiableAt ℂ riemannZeta s := by
        apply differentiableAt_riemannZeta
        intro hs
        simp [hs] at him
        rw [←him] at ht
        norm_num at ht
      have hl := horizontal_growth_lipschitz hf hd (z:=1+δ+I*t) (w:=1+I*t)
        (by simp; linarith) (by simp) (by simp) (by simp) hnδ hn0
      have hden : ‖(1:ℂ)+δ+I*t-(1+I*t)‖=δ := by
        rw [show (1:ℂ)+δ+I*t-(1+I*t)=(δ:ℂ) by ring,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
      rw [hden] at hl
      have hh := norm_add_le (riemannZeta (1+δ+I*t)-riemannZeta (1+I*t)) (riemannZeta (1+I*t))
      rw [sub_add_cancel] at hh
      linarith
    have hL2 : ‖riemannZeta (1+δ+2*I*t)‖ ≤ 2*K*P := by
      have hn : ‖(1:ℂ)+δ+2*I*t‖+2 ≤ 4*(|t|+2) := by
        simpa only [show I*((2*t:ℝ):ℂ)=2*I*t by push_cast; ring] using
          line_sample_norm hδ.le hδ1 (t:=t) (u:=2*t) (by rw [abs_mul]; norm_num)
      have hp := LFunction_norm_le_regular_add_pole (1:DirichletCharacter ℂ 1)
        (s:=1+δ+2*I*t) (by simp; linarith)
      rw [DirichletCharacter.LFunction_modOne_eq] at hp
      have hreg := hr 1 (1+δ+2*I*t) (by simp; linarith) hn
      have hden : 1 ≤ ‖(1:ℂ)+δ+2*I*t-1‖ := by
        have hb := Complex.abs_im_le_norm ((1:ℂ)+δ+2*I*t-1)
        simp [abs_mul] at hb
        linarith
      have hfrac : 1/‖(1:ℂ)+δ+2*I*t-1‖ ≤ 1 := div_le_one_of_le₀ hden (norm_nonneg _)
      linarith
    have hprod := (1:DirichletCharacter ℂ 1).norm_LFunction_product_ge_one hδ t
    simp only [one_pow,DirichletCharacter.LFunction_modOne_eq,norm_mul,norm_pow] at hprod
    have hL0' : ‖riemannZeta (1+δ)‖ ≤ 2*(K*P)/δ := by
      simpa only [DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq] using hL0
    exact hprod.trans (by gcongr)
  convert hh using 1
  field_simp
  ring

lemma zeta_high_line_lower {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 1 ≤ |t| →
      c*(|t|+2)^(-ε) ≤ ‖riemannZeta (1+I*t)‖ := by
  obtain ⟨K,hK,hg⟩ := zeta_high_line_bounds (by linarith : 0 < ε/14) (by linarith : ε/14 ≤ 1/2)
  have hK0 : 0 < K := by linarith
  refine ⟨1/(512*K^7),by positivity,?_⟩
  intro t ht
  let P : ℝ := (|t|+2)^(ε/7)
  have hP : 1 ≤ P := Real.one_le_rpow (by linarith [abs_nonneg t]) (by positivity)
  have he : 2*(ε/14)=ε/7 := by ring
  have hh := zeta_high_line_lower_aux ht hK hP
    (fun ψ s hs hn => by simpa only [he] using (hg t ht).1 ψ s hs hn)
    (fun s hs him hn => by simpa only [he] using (hg t ht).2 s hs him hn)
  have hP7 : P^7=(|t|+2)^ε := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast (by positivity : 0 ≤ |t|+2)]
    congr 1
    norm_num
  rw [hP7] at hh
  simpa only [Real.rpow_neg (by positivity : 0 ≤ |t|+2),div_eq_mul_inv] using hh

lemma zeta_high_strip_lower_aux {t c K P δ : ℝ} (ht : 1 ≤ |t|) (hc : 0<c) (hK : 1≤K) (hP : 1≤P)
    (hδ : 0≤δ) (hδ1 : δ≤1)
    (hr : ∀ ψ : DirichletCharacter ℂ 1,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P)
    (hd : ∀ s : ℂ,1 ≤ s.re → s.im=t → ‖s‖+2≤4*(|t|+2) → ‖deriv riemannZeta s‖≤K*P)
    (hl : c/P≤‖riemannZeta (1+I*t)‖) :
    (c/(4*K^2))/P^3≤‖riemannZeta (1+δ+I*t)‖ := by
  have hK0 : 0<K := by linarith
  have hP0 : 0<P := by linarith
  by_cases hnear : δ≤c/(2*K*P^2)
  · have hn0 : ‖(1:ℂ)+I*t‖+2≤4*(|t|+2) := by
      simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
    have hnδ := line_sample_norm hδ hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
    have hf (s : ℂ) (_hs : 1 ≤ s.re) (him : s.im=t) : DifferentiableAt ℂ riemannZeta s := by
      apply differentiableAt_riemannZeta
      intro hs
      simp [hs] at him
      rw [←him] at ht
      norm_num at ht
    have hdif := horizontal_growth_lipschitz hf hd
      (z:=1+I*t) (w:=1+δ+I*t) (by simp) (by simp; linarith) (by simp) (by simp) hn0 hnδ
    have hnorm : ‖(1:ℂ)+I*t-(1+δ+I*t)‖=δ := by
      rw [show (1:ℂ)+I*t-(1+δ+I*t)=-(δ:ℂ) by ring,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hδ]
    rw [hnorm] at hdif
    have hdb : ‖riemannZeta (1+I*t)-riemannZeta (1+δ+I*t)‖≤c/(2*P) := by
      apply hdif.trans
      calc
        K*P*δ ≤ K*P*(c/(2*K*P^2)) := mul_le_mul_of_nonneg_left hnear (by positivity)
        _ = _ := by field_simp
    have htri := norm_add_le (riemannZeta (1+I*t)-riemannZeta (1+δ+I*t)) (riemannZeta (1+δ+I*t))
    rw [sub_add_cancel] at htri
    have hva : c/(2*P)≤‖riemannZeta (1+δ+I*t)‖ := by
      have he : c/P=2*(c/(2*P)) := by ring
      rw [he] at hl
      linarith
    apply le_trans ?_ hva
    rw [div_div]
    apply div_le_div_of_nonneg_left hc.le (by positivity)
    have hP3 : P≤P^3 := by simpa using pow_le_pow_right₀ hP (show (1:ℕ)≤3 by norm_num)
    have hK2 : 1≤K^2 := one_le_pow₀ hK
    nlinarith [mul_le_mul_of_nonneg_left hP3 (show (0:ℝ)≤4*K^2 by positivity)]
  · have hδ0 : 0<δ := (by positivity : 0<c/(2*K*P^2)).trans (lt_of_not_ge hnear)
    have hInt := character_interior_lower (1:DirichletCharacter ℂ 1) hK hP hδ0 hδ1 hr
    rw [DirichletCharacter.LFunction_modOne_eq] at hInt
    apply le_trans ?_ hInt
    calc
      (c/(4*K^2))/P^3 = (c/(2*K*P^2))/(2*K*P) := by field_simp; norm_num
      _ ≤ δ/(2*K*P) := div_le_div_of_nonneg_right (le_of_not_ge hnear) (by positivity)

lemma zeta_high_strip_lower {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ,0<c ∧ ∀ σ t : ℝ, 1≤σ → σ≤2 → 1 ≤ |t| →
        c*(|t|+2)^(-ε)≤‖riemannZeta (σ+I*t)‖ := by
  obtain ⟨K,hK,hg⟩ := zeta_high_line_bounds (by linarith : 0<ε/6) (by linarith : ε/6≤1/2)
  obtain ⟨c,hc,hl⟩ := zeta_high_line_lower (by linarith : 0<ε/3) (by linarith : ε/3≤1)
  have hK0 : 0<K := by linarith
  refine ⟨c/(4*K^2),by positivity,?_⟩
  intro σ t hσ hσ2 ht
  let X : ℝ := (|t|+2)
  let P : ℝ := X^(ε/3)
  have hX : 1≤X := by dsimp [X]; linarith [abs_nonneg t]
  have hX0 : 0<X := by linarith
  have hP : 1≤P := Real.one_le_rpow hX (by positivity)
  have he : 2*(ε/6)=ε/3 := by ring
  have hl' : c/P≤‖riemannZeta (1+I*t)‖ := by
    have hh := hl t ht
    change c*X^(-(ε/3))≤_ at hh
    change c/X^(ε/3)≤_
    simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hh
  have hb := zeta_high_strip_lower_aux ht hc hK hP (δ:=σ-1) (by linarith) (by linarith)
    (fun ψ s hs hn => by simpa only [he] using (hg t ht).1 ψ s hs hn)
    (fun s hs him hn => by simpa only [he] using (hg t ht).2 s hs him hn) hl'
  have hP3 : P^3=X^ε := by dsimp [P]; rw [←Real.rpow_mul_natCast hX0.le]; congr 1; norm_num
  rw [hP3] at hb
  have hs : (1:ℂ)+((σ-1:ℝ):ℂ)+I*t=(σ:ℂ)+I*t := by push_cast; ring
  rw [hs] at hb
  change (c/(4*K^2))*X^(-ε)≤_
  simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hb

lemma principal_deriv_eq_regular {s : ℂ} (hs : 0 < s.re) :
    deriv (poleRemovedL (1:DirichletCharacter ℂ 1)) s = zetaRegular s+(s-1)*deriv zetaRegular s := by
  have he : poleRemovedL (1:DirichletCharacter ℂ 1) =ᶠ[𝓝 s] (fun z => (z-1)*zetaRegular z+1) := by
    filter_upwards [(continuous_re.tendsto s).eventually (lt_mem_nhds hs)] with z hz
    simpa only [poleRemovedL,ite_true] using poleRemovedZeta_eq hz
  have hh := (((hasDerivAt_id s).sub_const 1).mul (zetaRegular_differentiableAt hs).hasDerivAt).add_const 1
  rw [he.deriv_eq]
  simpa only [id_eq,one_mul,Pi.mul_apply] using hh.deriv

lemma principal_deriv_growth {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℂ, 1-ε/4 ≤ s.re →
      ‖deriv (poleRemovedL (1:DirichletCharacter ℂ 1)) s‖ ≤ K*(‖s‖+2)*(‖s‖+2)^ε := by
  obtain ⟨K,hK,hb⟩ := zetaRegular_bounds (by linarith : 0 < ε/2) (by linarith : ε/2 ≤ 1/2)
  have hK0 : 0 < K := by linarith
  refine ⟨K,hK0,?_⟩
  intro s hs
  obtain ⟨hl,hd⟩ := hb s (by linarith)
  rw [show 2*(ε/2)=ε by ring] at hl hd
  rw [principal_deriv_eq_regular (by linarith)]
  have hn : ‖s-1‖ ≤ ‖s‖+1 := by simpa using norm_sub_le s 1
  calc
    _ ≤ ‖zetaRegular s‖+‖s-1‖*‖deriv zetaRegular s‖ := by
      apply (norm_add_le _ _).trans_eq
      rw [norm_mul]
    _ ≤ K*(‖s‖+2)^ε+(‖s‖+1)*(K*(‖s‖+2)^ε) := by gcongr
    _ = _ := by ring

lemma principal_strip_lower {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
      c*(|t|+2)/((|t|+2)^ε) ≤ ‖poleRemovedL (1:DirichletCharacter ℂ 1) (σ+I*t)‖ := by
  obtain ⟨c₀,hc₀,hl⟩ := zeta_high_strip_lower hε hε1
  let F := poleRemovedL (1:DirichletCharacter ℂ 1)
  let S : Set ℂ := (fun p : ℝ×ℝ => (p.1:ℂ)+I*p.2) '' (Set.Icc 1 2 ×ˢ Set.Icc (-1) 1)
  have hS : IsCompact S := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hmem (z : ℂ) : z∈S ↔ 1 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ 1 := by
    constructor
    · rintro ⟨⟨u,v⟩,⟨hu,hv⟩,rfl⟩
      simpa [abs_le,and_assoc] using And.intro hu hv
    · rintro ⟨h₁,h₂,h₃⟩
      refine ⟨(z.re,z.im),⟨⟨h₁,h₂⟩,abs_le.mp h₃⟩,?_⟩
      simpa only [mul_comm] using Complex.re_add_im z
  have hc : ContinuousOn (fun z => (F z)⁻¹) S := by
    intro z hz
    exact (((poleRemovedL_differentiable 1).continuous.continuousAt).inv₀
      (poleRemovedL_ne_zero 1 ((hmem z).mp hz).1)).continuousWithinAt
  obtain ⟨M,hM⟩ := hS.exists_bound_of_continuousOn hc
  let D := max M 1
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let c := min (c₀/3) (1/(3*D))
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c,hc,?_⟩
  intro σ t hσ hσ2
  let z : ℂ := (σ:ℂ)+I*t
  have hz : 1 ≤ z.re := by simpa [z] using hσ
  have hT : 1 ≤ |t|+2 := by linarith [abs_nonneg t]
  have hP : 1 ≤ (|t|+2)^ε := Real.one_le_rpow hT hε.le
  by_cases ht : 1 ≤ |t|
  · have hz1 : z≠1 := by intro hh; have hi := congrArg Complex.im hh; simp [z] at hi; simp [hi] at ht; norm_num at ht
    have he : F z=(z-1)*riemannZeta z := by
      simp only [F,poleRemovedL,ite_true,DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hz1,
        DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq]
    have hnorm : (|t|+2)/3 ≤ ‖z-1‖ := by
      have hi := Complex.abs_im_le_norm (z-1)
      simp [z] at hi
      linarith
    have hlow := hl σ t hσ hσ2 ht
    rw [Real.rpow_neg (by positivity : 0 ≤ |t|+2),←div_eq_mul_inv] at hlow
    change c*(|t|+2)/( |t|+2)^ε ≤ ‖F z‖
    rw [he,norm_mul]
    calc
      _ ≤ (c₀/3)*(|t|+2)/(|t|+2)^ε := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)) (by positivity)
      _ = ((|t|+2)/3)*(c₀/(|t|+2)^ε) := by ring
      _ ≤ _ := mul_le_mul hnorm hlow (by positivity) (norm_nonneg _)
  · have ht1 : |t| ≤ 1 := le_of_not_ge ht
    have hzS : z∈S := (hmem z).mpr ⟨hz,by simpa [z] using hσ2,by simpa [z] using ht1⟩
    have hb := (hM z hzS).trans (le_max_left M 1)
    have hn : 0 < ‖F z‖ := norm_pos_iff.mpr (poleRemovedL_ne_zero 1 hz)
    rw [norm_inv,inv_eq_one_div] at hb
    have hlow : 1/D ≤ ‖F z‖ := by
      apply (div_le_iff₀ hD).mpr
      have hh := (div_le_iff₀ hn).mp hb
      nlinarith
    change c*(|t|+2)/(|t|+2)^ε ≤ ‖F z‖
    apply le_trans ?_ hlow
    calc
      _ ≤ c*(|t|+2) := div_le_self (by positivity) hP
      _ ≤ (1/(3*D))*3 := mul_le_mul (min_le_right _ _) (by linarith) (by positivity) (by positivity)
      _ = 1/D := by ring

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_PrincipalGrowth

section File_OpenAIPrimeGaps_RieszBounds

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Complex Filter Topology

noncomputable def logRiesz (f : ℂ → ℂ) (s : ℂ) : ℂ := (-deriv f s / f s)/(s*(s+1))

lemma near_line_denominator {z w : ℂ} {r : ℝ} (hz : 1 ≤  z.re) (hr : r ≤ 1/4)
    (hw : w∈Metric.closedBall z r) :
    w≠0 ∧ w+1≠0 ∧ (|z.im|+2)^2 ≤ 16*‖w‖*‖w+1‖ := by
  have hd : ‖w-z‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hw
  have hre := Complex.re_le_norm (z-w)
  rw [Complex.sub_re,norm_sub_rev] at hre
  have hwre : 3/4 ≤ w.re := by linarith
  have hw0 : w≠0 := by intro h; simp [h] at hwre; norm_num at hwre
  have hw1 : w+1≠0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hna : 3/4 ≤ ‖w‖ := hwre.trans (Complex.re_le_norm w)
  have hnb : 3/4 ≤ ‖w+1‖ := by
    have h := Complex.re_le_norm (w+1)
    simp only [Complex.add_re,Complex.one_re] at h
    linarith
  have ha : |z.im| ≤ ‖w‖+r := by
    have ht := norm_add_le (z-w) w
    rw [sub_add_cancel,norm_sub_rev] at ht
    linarith [Complex.abs_im_le_norm z]
  have hb : |z.im| ≤ ‖w+1‖+r := by
    have ht := norm_add_le (z-w) (w+1)
    rw [show z-w+(w+1)=z+1 by ring,norm_sub_rev] at ht
    have hi := Complex.abs_im_le_norm (z+1)
    simp only [Complex.add_im,Complex.one_im,add_zero] at hi
    linarith
  have ha' : |z.im|+2 ≤ 4*‖w‖ := by linarith
  have hb' : |z.im|+2 ≤ 4*‖w+1‖ := by linarith
  refine ⟨hw0,hw1,?_⟩
  have hp := mul_le_mul ha' hb' (by positivity : 0 ≤ |z.im|+2) (by positivity : 0 ≤ 4*‖w‖)
  nlinarith

lemma logRiesz_local {f : ℂ → ℂ} {z : ℂ} {r m M : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1/4) (hm : 0 < m) (hM : 0 ≤ M) (hz : 1 ≤  z.re)
    (hf : ∀ w∈Metric.closedBall z r,AnalyticAt ℂ f w)
    (hb : ∀ w∈Metric.closedBall z r,‖deriv f w‖ ≤ M)
    (hl : m ≤ ‖f z‖) (hMr : M*r ≤ m/2) :
    (∀ w∈Metric.closedBall z r,f w≠0) ∧
      DiffContOnCl ℂ (logRiesz f) (Metric.ball z r) ∧
      ∀ w∈Metric.closedBall z r,‖logRiesz f w‖ ≤ (32*M/m)/(|z.im|+2)^2 := by
  have hmem : z∈Metric.closedBall z r := Metric.mem_closedBall_self hr.le
  have hlo (w : ℂ) (hw : w∈Metric.closedBall z r) : m/2 ≤ ‖f w‖ := by
    have hd := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun w hw => (hf w hw).differentiableAt) hb (convex_closedBall z r) hw hmem
    have hdist : ‖z-w‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hw
    have hd' := hd.trans (mul_le_mul_of_nonneg_left hdist hM)
    have ht := norm_add_le (f z-f w) (f w)
    rw [sub_add_cancel] at ht
    linarith
  have hne (w : ℂ) (hw : w∈Metric.closedBall z r) : f w≠0 := by
    exact norm_pos_iff.mp ((by positivity : 0 < m/2).trans_le (hlo w hw))
  refine ⟨hne,?_,?_⟩
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr.ne']
    intro w hw
    obtain ⟨hw0,hw1,_⟩ := near_line_denominator hz hr1 hw
    exact (((hf w hw).deriv.neg.div (hf w hw) (hne w hw)).div
      (analyticAt_id.mul (analyticAt_id.add analyticAt_const)) (mul_ne_zero hw0 hw1)).differentiableWithinAt
  · intro w hw
    obtain ⟨hw0,hw1,hden⟩ := near_line_denominator hz hr1 hw
    have hnorm : 0 < ‖w‖*‖w+1‖ := mul_pos (norm_pos_iff.mpr hw0) (norm_pos_iff.mpr hw1)
    have hb₀ : ‖deriv f w‖/‖f w‖ ≤ 2*M/m := by
      apply (div_le_div₀ hM (hb w hw) (by positivity : 0 < m/2) (hlo w hw)).trans_eq
      ring
    have hb₁ : 1/(‖w‖*‖w+1‖) ≤ 16/(|z.im|+2)^2 := by
      apply (div_le_div_iff₀ hnorm (by positivity)).mpr
      nlinarith
    simp only [logRiesz,norm_div,norm_neg,norm_mul]
    calc
      _ = (‖deriv f w‖/‖f w‖)*(1/(‖w‖*‖w+1‖)) := by ring
      _  ≤  (2*M/m)*(16/(|z.im|+2)^2) := mul_le_mul hb₀ hb₁ (by positivity) (by positivity)
      _ = _ := by ring

lemma logRiesz_iteratedDeriv_bound {f : ℂ → ℂ} {z : ℂ} {r m M : ℝ}
    (n : ℕ) (hr : 0 < r) (hr1 : r ≤ 1/4) (hm : 0 < m) (hM : 0 ≤ M) (hz : 1 ≤  z.re)
    (hf : ∀ w∈Metric.closedBall z r,AnalyticAt ℂ f w)
    (hb : ∀ w∈Metric.closedBall z r,‖deriv f w‖ ≤ M)
    (hl : m ≤ ‖f z‖) (hMr : M*r ≤ m/2) :
    ‖iteratedDeriv n (logRiesz f) z‖ ≤ (n.factorial:ℝ)*((32*M/m)/(|z.im|+2)^2)/r^n := by
  have hh := logRiesz_local hr hr1 hm hM hz hf hb hl hMr
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hh.2.1
    (fun w hw => hh.2.2 w (Metric.sphere_subset_closedBall hw))

lemma logRiesz_power_bound {f : ℂ → ℂ} {z : ℂ} {P W c K d : ℝ} (n : ℕ)
    (hP : 1 ≤ P) (hW : 0 < W) (hc : 0 < c) (hK : 0 < K) (hd : 0 < d)
    (hd1 : d ≤ 1/4) (hKd : K*d ≤ c/2) (hz : 1 ≤ z.re)
    (hf : ∀ w∈Metric.closedBall z (d/P^2), AnalyticAt ℂ f w)
    (hb : ∀ w∈Metric.closedBall z (d/P^2), ‖deriv f w‖ ≤ K*W*P)
    (hl : c*W/P ≤ ‖f z‖) :
    ‖iteratedDeriv n (logRiesz f) z‖ ≤
      ((n.factorial:ℝ)*(32*K/c)/d^n)*P^(2*n+2)/(|z.im|+2)^2 := by
  have hP0 : 0 < P := by linarith
  have hr1 : d/P^2 ≤ 1/4 := by
    apply (div_le_self hd.le (one_le_pow₀ hP)).trans hd1
  have hMr : (K*W*P)*(d/P^2) ≤ (c*W/P)/2 := by
    calc
      _ = (K*d)*W/P := by field_simp
      _ ≤ (c/2)*W/P := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hKd hW.le) hP0.le
      _ = _ := by ring
  have hh := logRiesz_iteratedDeriv_bound n (by positivity : 0 < d/P^2) hr1
    (by positivity : 0 < c*W/P) (by positivity : 0 ≤ K*W*P) hz hf hb hl hMr
  apply hh.trans_eq
  rw [div_pow,pow_add,pow_mul]
  field_simp

lemma near_strip_geometry {σ t d P η : ℝ} (hσ : 1 ≤ σ) (hσ2 : σ ≤ 2)
    (hP : 1 ≤ P) (hd : 0 ≤ d) (hd1 : d ≤ 1/4) (hdη : d ≤ η/4)
    {w : ℂ} (hw : w∈Metric.closedBall ((σ:ℂ)+I*t) (d/P^2)) :
    1-η/4 ≤ w.re ∧ ‖w‖+2 ≤ 3*(|t|+2) := by
  have hr : d/P^2 ≤ d := div_le_self hd (one_le_pow₀ hP)
  have hdist : ‖w-((σ:ℂ)+I*t)‖ ≤ d/P^2 := by
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hw
  have hre := Complex.re_le_norm (((σ:ℂ)+I*t)-w)
  simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.I_re,Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_self,add_zero,norm_sub_rev] at hre
  have hnorm := norm_add_le (w-((σ:ℂ)+I*t)) ((σ:ℂ)+I*t)
  rw [sub_add_cancel] at hnorm
  have hnz := Complex.norm_le_abs_re_add_abs_im ((σ:ℂ)+I*t)
  simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,
    one_mul,sub_self,zero_add,add_zero,abs_of_nonneg (by linarith : 0 ≤ σ)] at hnz
  constructor <;> linarith [abs_nonneg t]

lemma nonprincipal_logRiesz_bound (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
        ‖iteratedDeriv n (logRiesz χ.LFunction) (σ+I*t)‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*(|t|+2)^(-(3/2:ℝ)) := by
  let ε : ℝ := 1/(4*(n+1:ℕ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    apply (div_le_one (by positivity : 0 < 4*((n+1:ℕ):ℝ))).mpr
    have hn : (1:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast (Nat.succ_pos n)
    linarith
  obtain ⟨c,hc,hl⟩ := nonprincipal_strip_lower hε hε1
  obtain ⟨K₀,hK₀,hb⟩ := LFunction_deriv_norm_small_power (by linarith : 0 < ε/2) (by linarith : ε/2 ≤ 1/2)
  let K := K₀*3^ε
  have hK : 0 < K := by dsimp [K]; positivity
  let d := min (min (1/4) (ε/4)) (c/(2*K))
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ 1/4 := (min_le_left _ _).trans (min_le_left _ _)
  have hdε : d ≤ ε/4 := (min_le_left _ _).trans (min_le_right _ _)
  have hKd : K*d ≤ c/2 := by
    have h := min_le_right (min (1/4) (ε/4)) (c/(2*K))
    change d ≤ c/(2*K) at h
    have hh := mul_le_mul_of_nonneg_left h hK.le
    have he : K*(c/(2*K))=c/2 := by field_simp
    rwa [he] at hh
  let D := (n.factorial:ℝ)*(32*K/c)/d^n
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro q _ χ hχp hχ σ t hσ hσ2
  let X : ℝ := ((q:ℝ)+2)*(|t|+2)
  let P : ℝ := X^ε
  have hX : 1 ≤ X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
  have hX0 : 0 < X := by linarith
  have hP : 1 ≤ P := Real.one_le_rpow hX hε.le
  have hlow : c*1/P ≤ ‖χ.LFunction (σ+I*t)‖ := by
    have h := hl q χ hχp hχ σ t hσ hσ2
    change c*X^(-ε) ≤ _ at h
    simpa only [mul_one,Real.rpow_neg hX0.le,div_eq_mul_inv] using h
  have hbound : ∀ w∈Metric.closedBall ((σ:ℂ)+I*t) (d/P^2), ‖deriv χ.LFunction w‖ ≤ K*1*P := by
    intro w hw
    obtain ⟨hre,hnorm⟩ := near_strip_geometry hσ hσ2 hP hd.le hd1 hdε hw
    have h := hb q χ hχ w (by linarith)
    rw [show 2*(ε/2)=ε by ring] at h
    have hn : ((q:ℝ)+2)*(‖w‖+2) ≤ 3*X := by
      dsimp [X]
      nlinarith [mul_nonneg (show (0:ℝ) ≤ q+2 by positivity) (sub_nonneg.mpr hnorm)]
    calc
      _ ≤ K₀*((q+2)*(‖w‖+2))^ε := h
      _ ≤ K₀*(3*X)^ε := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hn hε.le) hK₀.le
      _ = K*1*P := by rw [Real.mul_rpow (by norm_num) hX0.le]; dsimp [K,P]; ring
  have hh := logRiesz_power_bound n hP zero_lt_one hc hK hd hd1 hKd (by simpa using hσ)
    (fun w _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt w) hbound hlow
  have he : ε*(2*n+2:ℕ)=1/2 := by
    dsimp [ε]
    push_cast
    field_simp
    ring
  have hpow : P^(2*n+2)=X^(1/2:ℝ) := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast hX0.le,he]
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,zero_add] at hh
  change ‖iteratedDeriv n (logRiesz χ.LFunction) (σ+I*t)‖ ≤ D*P^(2*n+2)/(|t|+2)^2 at hh
  rw [hpow] at hh
  apply hh.trans_eq
  dsimp [X]
  rw [Real.mul_rpow (by positivity) (by positivity),Real.rpow_neg (by positivity : 0 ≤ |t|+2)]
  have ht : (|t|+2)^(1/2:ℝ)*(|t|+2)^(3/2:ℝ)=(|t|+2)^2 := by
    rw [←Real.rpow_add (by positivity),show (1/2:ℝ)+3/2=2 by norm_num]
    norm_num
  field_simp
  rw [←ht]

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_RieszBounds

section File_OpenAIPrimeGaps_MellinSmoothing

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Complex Real Set MeasureTheory Filter Topology

noncomputable def rieszKernel : ℝ → ℂ := (Ioc 0 1).indicator (fun t => 1-(t:ℂ))

lemma hasMellin_rieszKernel {s : ℂ} (hs : 0<s.re) :
    HasMellin rieszKernel s (1/(s*(s+1))) := by
  have h₀ := hasMellin_one_Ioc hs
  have h₁ := hasMellin_cpow_Ioc 1 (by simp; linarith : 0<s.re+(1:ℂ).re)
  have hh := hasMellin_sub h₀.1 h₁.1
  rw [h₀.2,h₁.2] at hh
  have he : (fun t : ℝ => (Ioc 0 1).indicator (fun _ : ℝ => (1:ℂ)) t-
      (Ioc 0 1).indicator (fun t : ℝ => (t:ℂ)^(1:ℂ)) t)=rieszKernel := by
    ext t
    by_cases ht : t∈Ioc (0:ℝ) 1 <;> simp [rieszKernel,ht]
  rw [he] at hh
  have hs0 : s≠0 := by intro h; simp [h] at hs
  have hs1 : s+1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have heval : 1/s-1/(s+1)=1/(s*(s+1)) := by field_simp; ring
  rwa [heval] at hh

lemma rieszKernel_eq_max {x : ℝ} (hx : 0<x) : rieszKernel x=(max (1-x) 0:ℝ) := by
  by_cases hx1 : x≤1
  · simp [rieszKernel,Set.mem_Ioc,hx,hx1]
  · simp [rieszKernel,Set.mem_Ioc,hx,hx1,max_eq_right (by linarith : 1-x≤(0:ℝ))]

lemma rieszKernel_continuousAt {x : ℝ} (hx : 0<x) : ContinuousAt rieszKernel x := by
  have he : rieszKernel =ᶠ[𝓝 x] (fun x : ℝ => ((max (1-x) 0:ℝ):ℂ)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact rieszKernel_eq_max hy
  exact (show ContinuousAt (fun x : ℝ => ((max (1-x) 0:ℝ):ℂ)) x by fun_prop).congr he.symm

lemma rieszDenominator_bound {s : ℂ} (hs : 1≤ s.re) :
    ‖1/(s*(s+1))‖≤2/(1+s.im^2) := by
  have ha : 1≤‖s‖ := hs.trans (Complex.re_le_norm s)
  have hb : 1≤‖s+1‖ := by have h := Complex.re_le_norm (s+1); simp at h; linarith
  have hai : |s.im|≤‖s‖ := Complex.abs_im_le_norm s
  have hbi : |s.im|≤‖s+1‖ := by simpa using Complex.abs_im_le_norm (s+1)
  have hp : 1≤‖s‖*‖s+1‖ := one_le_mul_of_one_le_of_one_le ha hb
  have hpi : s.im^2≤‖s‖*‖s+1‖ := by
    simpa only [←sq, sq_abs] using mul_le_mul hai hbi (abs_nonneg _) (norm_nonneg _)
  rw [norm_div,norm_one,norm_mul]
  apply (div_le_div_iff₀ (by positivity : 0<‖s‖*‖s+1‖) (by positivity : 0<1+s.im^2)).mpr
  nlinarith

lemma rieszDenominator_verticalIntegrable {σ : ℝ} (hσ : 1≤σ) :
    VerticalIntegrable (fun s : ℂ => 1/(s*(s+1))) σ := by
  have hne (t : ℝ) : (σ:ℂ)+(t:ℂ)*I≠0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hne1 (t : ℝ) : (σ:ℂ)+(t:ℂ)*I+1≠0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hm : Continuous (fun t : ℝ => 1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro t
    exact mul_ne_zero (hne t) (hne1 t)
  apply (integrable_inv_one_add_sq.const_mul 2).mono' hm.aestronglyMeasurable
  filter_upwards [] with t
  have hb := rieszDenominator_bound (s:=(σ:ℂ)+t*I) (by simpa using hσ)
  simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,mul_zero,
    Complex.ofReal_re,Complex.I_im,mul_one,add_zero,zero_add,div_eq_mul_inv] using hb

lemma rieszKernel_mellinInv {σ x : ℝ} (hσ : 1≤σ) (hx : 0<x) :
    mellinInv σ (fun s : ℂ => 1/(s*(s+1))) x=rieszKernel x := by
  have hσ0 : (0:ℝ)<σ := by linarith
  have hm (t : ℝ) : mellin rieszKernel (σ+t*I)=1/((σ+t*I)*(σ+t*I+1)) :=
    (hasMellin_rieszKernel (by simpa using hσ0)).2
  have hF : VerticalIntegrable (mellin rieszKernel) σ := by
    unfold VerticalIntegrable
    simp_rw [hm]
    exact rieszDenominator_verticalIntegrable hσ
  rw [←mellinInv_mellin_eq σ rieszKernel hx (hasMellin_rieszKernel (by simpa using hσ0)).1 hF
    (rieszKernel_continuousAt hx)]
  simp only [mellinInv,hm]

open Complex Filter Topology

lemma principal_logRiesz_bound (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
        ‖iteratedDeriv n (logRiesz (poleRemovedL (1:DirichletCharacter ℂ 1))) (σ+I*t)‖ ≤
          D*(|t|+2)^(-(3/2:ℝ)) := by
  let ε : ℝ := 1/(4*(n+1:ℕ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    apply (div_le_one (by positivity : 0 < 4*((n+1:ℕ):ℝ))).mpr
    have hn : (1:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast (Nat.succ_pos n)
    linarith
  obtain ⟨c,hc,hl⟩ := principal_strip_lower hε hε1
  obtain ⟨K₀,hK₀,hb⟩ := principal_deriv_growth hε hε1
  let K := 3*K₀*3^ε
  have hK : 0 < K := by dsimp [K]; positivity
  let d := min (min (1/4) (ε/4)) (c/(2*K))
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ 1/4 := (min_le_left _ _).trans (min_le_left _ _)
  have hdε : d ≤ ε/4 := (min_le_left _ _).trans (min_le_right _ _)
  have hKd : K*d ≤ c/2 := by
    have h := min_le_right (min (1/4) (ε/4)) (c/(2*K))
    change d ≤ c/(2*K) at h
    have hh := mul_le_mul_of_nonneg_left h hK.le
    have he : K*(c/(2*K))=c/2 := by field_simp
    rwa [he] at hh
  let D := (n.factorial:ℝ)*(32*K/c)/d^n
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro σ t hσ hσ2
  let X : ℝ := (|t|+2)
  let P : ℝ := X^ε
  have hX : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg t]
  have hX0 : 0 < X := by linarith
  have hP : 1 ≤ P := Real.one_le_rpow hX hε.le
  have hlow : c*(|t|+2)/P ≤ ‖poleRemovedL (1:DirichletCharacter ℂ 1) (σ+I*t)‖ := hl σ t hσ hσ2
  have hbound : ∀ w∈Metric.closedBall ((σ:ℂ)+I*t) (d/P^2),
      ‖deriv (poleRemovedL (1:DirichletCharacter ℂ 1)) w‖ ≤ K*(|t|+2)*P := by
    intro w hw
    obtain ⟨hre,hnorm⟩ := near_strip_geometry hσ hσ2 hP hd.le hd1 hdε hw
    have h := hb w hre
    calc
      _ ≤ K₀*(‖w‖+2)*(‖w‖+2)^ε := h
      _ ≤ K₀*(3*X)*(3*X)^ε := by gcongr
      _ = K*(|t|+2)*P := by rw [Real.mul_rpow (by norm_num) hX0.le]; dsimp [K,P,X]; ring
  have hh := logRiesz_power_bound n hP (by positivity : 0 < |t|+2) hc hK hd hd1 hKd (by simpa using hσ)
    (fun w _ => (poleRemovedL_differentiable (1:DirichletCharacter ℂ 1)).analyticAt w) hbound hlow
  have he : ε*(2*n+2:ℕ)=1/2 := by
    dsimp [ε]
    push_cast
    field_simp
    ring
  have hpow : P^(2*n+2)=X^(1/2:ℝ) := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast hX0.le,he]
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,zero_add] at hh
  change ‖iteratedDeriv n (logRiesz (poleRemovedL (1:DirichletCharacter ℂ 1))) (σ+I*t)‖ ≤ D*P^(2*n+2)/(|t|+2)^2 at hh
  rw [hpow] at hh
  apply hh.trans_eq
  dsimp [X]
  rw [Real.rpow_neg (by positivity : 0 ≤ |t|+2)]
  have ht : (|t|+2)^(1/2:ℝ)*(|t|+2)^(3/2:ℝ)=(|t|+2)^2 := by
    rw [←Real.rpow_add (by positivity),show (1/2:ℝ)+3/2=2 by norm_num]
    norm_num
  field_simp
  rw [←ht]

lemma primitive_logRiesz_bound (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
        ‖iteratedDeriv n (logRiesz (poleRemovedL χ)) (σ+I*t)‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*(|t|+2)^(-(3/2:ℝ)) := by
  obtain ⟨D₀,hD₀,h₀⟩ := nonprincipal_logRiesz_bound n
  obtain ⟨D₁,hD₁,h₁⟩ := principal_logRiesz_bound n
  refine ⟨max D₀ D₁,lt_of_lt_of_le hD₀ (le_max_left _ _),?_⟩
  intro q _ χ hχp σ t hσ hσ2
  have hq : 1 ≤ ((q:ℝ)+2)^(1/2:ℝ) := Real.one_le_rpow (by linarith [Nat.cast_nonneg (α:=ℝ) q]) (by norm_num)
  by_cases hχ : χ=1
  · subst χ
    have hq1 : q=1 := by simpa [DirichletCharacter.IsPrimitive,DirichletCharacter.conductor_one] using hχp.symm
    subst q
    have hq' : 1 ≤ ((1:ℝ)+2)^(1/2:ℝ) := by simpa only [Nat.cast_one] using hq
    have hb := h₁ σ t hσ hσ2
    apply hb.trans
    have hc : D₁ ≤ max D₀ D₁*((1:ℝ)+2)^(1/2:ℝ) := by
      calc
        D₁ ≤ max D₀ D₁ := le_max_right _ _
        _ ≤ _ := le_mul_of_one_le_right (le_trans hD₀.le (le_max_left _ _)) hq'
    simpa only [Nat.cast_one] using mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (|t|+2)^(-(3/2:ℝ)))
  · have hb := h₀ q χ hχp hχ σ t hσ hσ2
    simp only [poleRemovedL,hχ,ite_false]
    apply hb.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)

lemma logRiesz_poleRemoved_analyticAt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 ≤ s.re) : AnalyticAt ℂ (logRiesz (poleRemovedL χ)) s := by
  have h₀ : s≠0 := by intro h; simp [h] at hs; norm_num at hs
  have h₁ : s+1≠0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith
  exact (primeLogDerivativeRegular_analyticAt χ (poleRemovedL_ne_zero χ hs)).div
    (analyticAt_id.mul (analyticAt_id.add analyticAt_const)) (mul_ne_zero h₀ h₁)

open Complex Filter Topology MeasureTheory

open scoped FourierTransform

lemma analyticAt_iteratedDeriv_local {f : ℂ → ℂ} {z : ℂ} (h : AnalyticAt ℂ f z) (n : ℕ) :
    AnalyticAt ℂ (iteratedDeriv n f) z := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

lemma vertical_contDiff {f : ℂ → ℂ} {z a : ℂ}
    (hf : ∀ t : ℝ, AnalyticAt ℂ f (z+a*t)) :
    ContDiff ℝ ⊤ (fun t : ℝ => f (z+a*t)) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have hr : ContDiffAt ℝ ⊤ (fun t : ℝ => (t:ℂ)) t := Complex.ofRealCLM.contDiff.contDiffAt
  exact ((hf t).contDiffAt.restrict_scalars ℝ).comp t
    (contDiffAt_const.add (contDiffAt_const.mul hr))

lemma vertical_iteratedDeriv {f : ℂ → ℂ} {z a : ℂ}
    (hf : ∀ t : ℝ, AnalyticAt ℂ f (z+a*t)) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => f (z+a*t)) =
      fun t : ℝ => a^n * iteratedDeriv n f (z+a*t) := by
  induction n with
  | zero => ext t; simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    have ha : HasDerivAt (fun t : ℝ => z+a*t) a t := by
      convert (((hasDerivAt_id (t:ℂ)).const_mul a).const_add z).comp_ofReal using 1 <;> simp
    have hd := ((analyticAt_iteratedDeriv_local (hf t) n).differentiableAt.hasDerivAt.comp t ha).const_mul (a^n)
    rw [iteratedDeriv_succ]
    simpa only [Function.comp_def,pow_succ,mul_assoc,mul_comm,mul_left_comm] using hd.deriv

noncomputable def decayMajorant (t : ℝ) : ℝ := (1+|t|)^(-(3/2:ℝ))

lemma decayMajorant_nonneg (t : ℝ) : 0 ≤ decayMajorant t := by dsimp [decayMajorant]; positivity

lemma decayMajorant_integrable : Integrable decayMajorant := by
  change Integrable (fun t : ℝ => (1+|t|)^(-(3/2:ℝ)))
  simpa only [Real.norm_eq_abs] using
    (integrable_one_add_norm (E:=ℝ) (by norm_num : (Module.finrank ℝ ℝ:ℝ) < 3/2))

lemma integrable_of_decay_bound {g : ℝ → ℂ} {M : ℝ} (hg : Continuous g)
    (hb : ∀ t, ‖g t‖ ≤ M*decayMajorant t) : Integrable g := by
  exact (decayMajorant_integrable.const_mul M).mono' hg.aestronglyMeasurable (Filter.Eventually.of_forall hb)

lemma integral_norm_le_of_decay_bound {g : ℝ → ℂ} {M : ℝ} (hg : Continuous g)
    (hb : ∀ t, ‖g t‖ ≤ M*decayMajorant t) :
    ∫ t, ‖g t‖ ≤ M*(∫ t, decayMajorant t) := by
  rw [←integral_const_mul]
  exact integral_mono (integrable_of_decay_bound hg hb).norm
    (decayMajorant_integrable.const_mul M) hb

lemma fourierInv_decay {g : ℝ → ℂ} (hg : ContDiff ℝ ⊤ g)
    (hi : ∀ n : ℕ, Integrable (iteratedDeriv n g)) (n : ℕ) {M u : ℝ}
    (hb : (∫ t, ‖iteratedDeriv n g t‖) ≤ M) (hu : 0 < |u|) :
    ‖𝓕⁻ g u‖ ≤ M/|u|^n := by
  have he := congrFun (Real.fourier_iteratedDeriv (N:=⊤) (hg.of_le le_top) (fun n _ => hi n) (n:=n) (by simp)) (-u)
  have hn := VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
    (innerₗ ℝ) (iteratedDeriv n g) (-u)
  change ‖𝓕 (iteratedDeriv n g) (-u)‖ ≤ _ at hn
  have hn' := hn.trans hb
  rw [he,norm_smul,norm_pow] at hn'
  have hc : ‖(2:ℂ)*Real.pi*I*(-u)‖=2*Real.pi*|u| := by
    simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  simp only [Complex.ofReal_neg] at hn'
  rw [hc] at hn'
  rw [Real.fourierInv_eq_fourier_neg]
  apply (le_div_iff₀ (pow_pos hu n)).mpr
  have hπ : (1:ℝ) ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  have hpow : |u|^n ≤ (2*Real.pi*|u|)^n := by
    gcongr
    exact le_mul_of_one_le_left hu.le hπ
  nlinarith [mul_le_mul_of_nonneg_right hpow (norm_nonneg (𝓕 g (-u)))]

open Complex Real Set MeasureTheory Filter Topology

lemma mellinInv_const_mul (σ : ℝ) (f : ℂ → ℂ) (a : ℂ) (x : ℝ) :
    mellinInv σ (fun s => a*f s) x=a*mellinInv σ f x := by
  simp [mellinInv,smul_eq_mul,Complex.real_smul,mul_left_comm,integral_const_mul,mul_assoc]

lemma mellinInv_term_riesz {σ y : ℝ} (hσ : 1≤σ) (hy : 0<y)
    (a : ℕ → ℂ) (n : ℕ) :
    mellinInv σ (fun s => LSeries.term a s n/(s*(s+1))) y=
      if n=0 then 0 else a n*rieszKernel ((n:ℝ)*y) := by
  by_cases hn : n=0
  · simp [hn,mellinInv]
  rw [ite_eq_right hn]
  have hi := rieszKernel_mellinInv hσ (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hy)
  rw [←hi]
  simp only [mellinInv,LSeries.term_of_ne_zero hn,smul_eq_mul,Complex.real_smul]
  rw [mul_left_comm (a n) ((1/(2*π):ℝ):ℂ)]
  congr 1
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg n) hy.le]
  simp only [Complex.ofReal_natCast,Complex.cpow_neg]
  ring

lemma riesz_inverse_integrand_norm {σ y : ℝ} (hy : 0<y) (a : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    ‖(y:ℂ)^(-((σ:ℂ)+t*I))*(LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))‖=
      (y^(-σ)*‖LSeries.term a (σ:ℂ) n‖)*‖1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))‖ := by
  simp only [norm_mul,norm_div,norm_one,Complex.norm_cpow_eq_rpow_re_of_pos hy,
    Complex.neg_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero,LSeries.norm_term_eq]
  ring

lemma riesz_inverse_integrand_summable {σ y : ℝ} (hσ : 1≤σ) (hy : 0<y)
    (a : ℕ → ℂ) (ha : LSeriesSummable a (σ:ℂ)) :
    (∀ n : ℕ, Integrable (fun t : ℝ => (y:ℂ)^(-((σ:ℂ)+t*I))*
        (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))))) ∧
    Summable (fun n : ℕ => ∫ t : ℝ, ‖(y:ℂ)^(-((σ:ℂ)+t*I))*
        (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))‖) := by
  have hc (n : ℕ) : Continuous (fun t : ℝ => (y:ℂ)^(-((σ:ℂ)+t*I))*
      (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))) := by
    have hz (t : ℝ) : (σ:ℂ)+t*I≠0 := by
      intro hh; have := congrArg Complex.re hh; simp at this; linarith
    have hz1 (t : ℝ) : (σ:ℂ)+t*I+1≠0 := by
      intro hh; have := congrArg Complex.re hh; simp at this; linarith
    have hd : Continuous (fun t : ℝ => ((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)) := by fun_prop
    have he : Continuous (fun t : ℝ => -((σ:ℂ)+t*I)) := by fun_prop
    apply (he.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).mul
    apply Continuous.div _ hd (fun t => mul_ne_zero (hz t) (hz1 t))
    by_cases hn : n=0
    · simpa [hn] using (continuous_const : Continuous (fun _t : ℝ => (0:ℂ)))
    · simp only [LSeries.term_of_ne_zero hn]
      apply continuous_const.div
      · exact (show Continuous (fun t : ℝ => (σ:ℂ)+t*I) by fun_prop).const_cpow
          (.inl (Nat.cast_ne_zero.mpr hn))
      · intro t; exact Complex.cpow_ne_zero_iff.mpr (.inl (Nat.cast_ne_zero.mpr hn))
  have hnorm (n : ℕ) : Integrable (fun t : ℝ => ‖(y:ℂ)^(-((σ:ℂ)+t*I))*
      (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))‖) := by
    simp_rw [riesz_inverse_integrand_norm hy]
    exact (rieszDenominator_verticalIntegrable hσ).norm.const_mul _
  refine ⟨fun n => (integrable_norm_iff (hc n).aestronglyMeasurable).mp (hnorm n), ?_⟩
  simp_rw [riesz_inverse_integrand_norm hy,integral_const_mul]
  exact (ha.norm.mul_left (y^(-σ))).mul_right _

lemma mellinInv_LSeries_riesz {σ y : ℝ} (hσ : 1≤σ) (hy : 0<y)
    (a : ℕ → ℂ) (ha : LSeriesSummable a (σ:ℂ)) :
    mellinInv σ (fun s => LSeries a s/(s*(s+1))) y=
      ∑' n : ℕ, if n=0 then 0 else a n*rieszKernel ((n:ℝ)*y) := by
  obtain ⟨hi,hs⟩ := riesz_inverse_integrand_summable hσ hy a ha
  have he := integral_tsum_of_summable_integral_norm hi hs
  simp only [mellinInv,smul_eq_mul,Complex.real_smul]
  simp only [LSeries,←tsum_div_const,←tsum_mul_left]
  rw [←he,←tsum_mul_left]
  apply tsum_congr
  intro n
  exact mellinInv_term_riesz hσ hy a n

noncomputable def rieszSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n*(1-(n:ℂ)/(x:ℂ))

lemma rieszKernel_tsum_eq {x : ℝ} (hx : 0<x) (a : ℕ → ℂ) :
    (∑' n : ℕ, if n=0 then 0 else a n*rieszKernel ((n:ℝ)*(1/x)))=rieszSum a x := by
  classical
  rw [tsum_eq_sum (s:=Finset.Ioc 0 ⌊x⌋₊)]
  · apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn0,hnx⟩ := Finset.mem_Ioc.mp hn
    have hn0' : (0:ℝ)<n := by exact_mod_cast hn0
    have hnx' : (n:ℝ)≤x := (Nat.le_floor_iff hx.le).mp hnx
    have hm0 : 0<(n:ℝ)*(1/x) := mul_pos hn0' (one_div_pos.mpr hx)
    have hm1 : (n:ℝ)*(1/x)≤1 := by rw [mul_one_div]; exact (div_le_one hx).mpr hnx'
    rw [ite_eq_right (by omega : n≠0),rieszKernel,
      Set.indicator_of_mem (show (n:ℝ)*(1/x)∈Ioc (0:ℝ) 1 from ⟨hm0,hm1⟩)]
    push_cast
    ring
  · intro n hn
    by_cases hn0 : n=0
    · simp [hn0]
    have hnx : x<(n:ℝ) := by
      have hnot : ¬n≤⌊x⌋₊ := by intro h; exact hn (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0,h⟩)
      exact lt_of_not_ge (fun h => hnot ((Nat.le_floor_iff hx.le).mpr h))
    have hm1 : ¬(n:ℝ)*(1/x)≤1 := by rw [mul_one_div]; exact not_le.mpr ((lt_div_iff₀ hx).mpr (by simpa using hnx))
    rw [ite_eq_right hn0,rieszKernel,
      Set.indicator_of_notMem (show (n:ℝ)*(1/x)∉Ioc (0:ℝ) 1 from fun h => hm1 h.2),mul_zero]

lemma rieszSum_mellinInv {σ x : ℝ} (hσ : 1≤σ) (hx : 0<x)
    (a : ℕ → ℂ) (ha : LSeriesSummable a (σ:ℂ)) :
    mellinInv σ (fun s => LSeries a s/(s*(s+1))) (1/x)=rieszSum a x := by
  rw [mellinInv_LSeries_riesz hσ (one_div_pos.mpr hx) a ha,rieszKernel_tsum_eq hx]

open Complex Real Set MeasureTheory Filter Topology

noncomputable def poleRieszKernel (y : ℝ) : ℂ :=
  (1/2:ℂ)*((y:ℂ)^(-1:ℂ)*rieszKernel y-rieszKernel y)

lemma hasMellin_poleRieszKernel {s : ℂ} (hs : 1<s.re) :
    HasMellin poleRieszKernel s (1/((s-1)*s*(s+1))) := by
  have h₀ := hasMellin_rieszKernel (s:=s) (by linarith)
  have h₁ := hasMellin_rieszKernel (s:=s+(-1)) (by simp; linarith)
  have hshift : MellinConvergent (fun t : ℝ => (t:ℂ)^(-1:ℂ) • rieszKernel t) s :=
    MellinConvergent.cpow_smul.mpr h₁.1
  have hm := mellin_cpow_smul rieszKernel s (-1)
  have hh := hasMellin_sub hshift h₀.1
  rw [hm,h₁.2,h₀.2] at hh
  have hhalf := hasMellin_const_smul hh.1 (1/2:ℂ)
  rw [hh.2] at hhalf
  have he : (1/2:ℂ) • (1/((s+-1)*(s+-1+1))-1/(s*(s+1)))=
      1/((s-1)*s*(s+1)) := by
    have hs0 : s≠0 := by intro h; simp [h] at hs; norm_num at hs
    have hs1 : s-1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    have hs2 : s+1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [show s+-1+1=s by ring,←sub_eq_add_neg]
    simp only [smul_eq_mul]
    field_simp [hs0,hs1,hs2]
    ring
  rw [he] at hhalf
  change HasMellin (fun t : ℝ => (1/2:ℂ)*((t:ℂ)^(-1:ℂ)*rieszKernel t-rieszKernel t)) s _
  simpa only [smul_eq_mul] using hhalf

lemma poleRieszKernel_continuousAt {y : ℝ} (hy : 0<y) :
    ContinuousAt poleRieszKernel y := by
  apply continuousAt_const.mul
  apply ContinuousAt.sub _ (rieszKernel_continuousAt hy)
  apply ContinuousAt.mul _ (rieszKernel_continuousAt hy)
  simp only [Complex.cpow_neg_one]
  have hr : ContinuousAt (fun t : ℝ => (t:ℂ)) y := Complex.continuous_ofReal.continuousAt
  exact hr.inv₀ (Complex.ofReal_ne_zero.mpr hy.ne')

lemma poleRiesz_verticalIntegrable {σ : ℝ} (hσ : 1<σ) :
    VerticalIntegrable (fun s : ℂ => 1/((s-1)*s*(s+1))) σ := by
  have hn (t : ℝ) : ((σ:ℂ)+t*I-1)*((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)≠0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · intro h; have := congrArg Complex.re h; simp at this; linarith
      · intro h; have := congrArg Complex.re h; simp at this; linarith
    · intro h; have := congrArg Complex.re h; simp at this; linarith
  have hc : Continuous (fun t : ℝ => 1/(((σ:ℂ)+t*I-1)*((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))) :=
    continuous_const.div (by fun_prop) hn
  apply ((rieszDenominator_verticalIntegrable hσ.le).norm.const_mul (1/(σ-1))).mono'
    hc.aestronglyMeasurable
  filter_upwards [] with t
  rw [norm_div,norm_one,norm_mul,norm_mul]
  have hl : σ-1 ≤ ‖(σ:ℂ)+t*I-1‖ := by simpa using Complex.re_le_norm ((σ:ℂ)+t*I-1)
  have hn0 : 0<‖(σ:ℂ)+t*I-1‖ := lt_of_lt_of_le (by linarith) hl
  have hh : 1/‖(σ:ℂ)+t*I-1‖ ≤ 1/(σ-1) := one_div_le_one_div_of_le (by linarith) hl
  simpa only [norm_div,norm_one,norm_mul,div_eq_mul_inv,mul_inv_rev,norm_inv,mul_assoc,mul_comm,mul_left_comm,one_mul,mul_one]
    using mul_le_mul_of_nonneg_right hh (norm_nonneg (1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))))

lemma poleRiesz_mellinInv {σ y : ℝ} (hσ : 1<σ) (hy : 0<y) :
    mellinInv σ (fun s : ℂ => 1/((s-1)*s*(s+1))) y=poleRieszKernel y := by
  have hm (t : ℝ) : mellin poleRieszKernel (σ+t*I)=1/((σ+t*I-1)*(σ+t*I)*(σ+t*I+1)) :=
    (hasMellin_poleRieszKernel (by simpa using hσ)).2
  have hf : VerticalIntegrable (mellin poleRieszKernel) σ := by
    unfold VerticalIntegrable
    simp_rw [hm]
    exact poleRiesz_verticalIntegrable hσ
  rw [←mellinInv_mellin_eq σ poleRieszKernel hy
    (hasMellin_poleRieszKernel (by simpa using hσ)).1 hf (poleRieszKernel_continuousAt hy)]
  simp only [mellinInv,hm]

lemma poleRieszKernel_inv {x : ℝ} (hx : 1≤x) :
    poleRieszKernel (1/x)=((x/2-1+1/(2*x):ℝ):ℂ) := by
  have hx0 : 0<x := by linarith
  have hy : 0<1/x := one_div_pos.mpr hx0
  have hy1 : 1/x≤1 := (div_le_one hx0).mpr hx
  rw [poleRieszKernel,rieszKernel_eq_max hy,max_eq_left (by linarith : 0≤1-1/x)]
  simp only [Complex.cpow_neg_one,Complex.ofReal_div,Complex.ofReal_one,inv_div,div_one,
    Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_ofNat]
  have hn : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  field_simp
  ring

lemma mellinInv_integrable {σ y : ℝ} (hy : 0<y) {f : ℂ → ℂ}
    (hf : VerticalIntegrable f σ) :
    Integrable (fun t : ℝ => (y:ℂ)^(-((σ:ℂ)+t*I))*f ((σ:ℂ)+t*I)) := by
  have he : Continuous (fun t : ℝ => -((σ:ℂ)+t*I)) := by fun_prop
  have hc := he.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hy.ne'))
  apply (hf.norm.const_mul (y^(-σ))).mono' (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with t
  change ‖(y:ℂ)^(-((σ:ℂ)+t*I))*f ((σ:ℂ)+t*I)‖ ≤ y^(-σ)*‖f ((σ:ℂ)+t*I)‖
  simp only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy,Complex.neg_re,
    Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    mul_zero,zero_mul,sub_self,add_zero,le_refl]

lemma mellinInv_add_of_verticalIntegrable {σ y : ℝ} (hy : 0<y) {f g : ℂ → ℂ}
    (hf : VerticalIntegrable f σ) (hg : VerticalIntegrable g σ) :
    mellinInv σ (fun s => f s+g s) y=mellinInv σ f y+mellinInv σ g y := by
  simp only [mellinInv,smul_eq_mul,Complex.real_smul,mul_add]
  rw [integral_add (mellinInv_integrable hy hf) (mellinInv_integrable hy hg),mul_add]

open Complex Real Set MeasureTheory Filter Topology

open scoped FourierTransform

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_MellinSmoothing

section File_OpenAIPrimeGaps_RieszDecay

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Complex Real Set MeasureTheory Filter Topology

open Complex Filter Topology

open Complex Filter Topology MeasureTheory

open scoped FourierTransform

open Complex Real Set MeasureTheory Filter Topology

open Complex Real Set MeasureTheory Filter Topology

open Complex Real Set MeasureTheory Filter Topology

open scoped FourierTransform

noncomputable def logRieszVertical {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) : ℂ := logRiesz (poleRemovedL χ) (σ+2*π*t*I)

lemma logRieszVertical_contDiff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1≤σ) : ContDiff ℝ ⊤ (logRieszVertical χ σ) := by
  have h : ∀ t : ℝ, AnalyticAt ℂ (logRiesz (poleRemovedL χ)) ((σ:ℂ)+(2*π*I)*(t:ℂ)) := by
    intro t
    apply logRiesz_poleRemoved_analyticAt
    simpa using hσ
  convert vertical_contDiff h using 1
  ext t
  dsimp [logRieszVertical]
  congr 1
  ring

lemma logRieszVertical_iteratedDeriv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1≤σ) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (logRieszVertical χ σ) t=
      ((2:ℂ)*π*I)^n*iteratedDeriv n (logRiesz (poleRemovedL χ)) (σ+2*π*t*I) := by
  have h : ∀ t : ℝ, AnalyticAt ℂ (logRiesz (poleRemovedL χ)) ((σ:ℂ)+(2*π*I)*(t:ℂ)) := by
    intro t
    apply logRiesz_poleRemoved_analyticAt
    simpa using hσ
  have he : logRieszVertical χ σ=(fun t : ℝ => logRiesz (poleRemovedL χ) ((σ:ℂ)+(2*π*I)*(t:ℂ))) := by
    ext t
    dsimp [logRieszVertical]
    congr 1
    ring
  simpa only [he,mul_assoc,mul_comm,mul_left_comm] using congrFun (vertical_iteratedDeriv h n) t

lemma logRieszVertical_bound (n : ℕ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ σ t : ℝ, 1≤σ → σ≤2 →
        ‖iteratedDeriv n (logRieszVertical χ σ) t‖ ≤
          (D*((q:ℝ)+2)^(1/2:ℝ))*decayMajorant t := by
  obtain ⟨D,hD,hb⟩ := primitive_logRiesz_bound n
  refine ⟨(2*π)^n*D,by positivity,?_⟩
  intro q _ χ hp σ t hσ hσ2
  have he : (σ:ℂ)+2*π*t*I=(σ:ℂ)+I*((2*π*t:ℝ):ℂ) := by push_cast; ring
  rw [logRieszVertical_iteratedDeriv χ hσ,norm_mul,norm_pow,he]
  have hc : ‖(2:ℂ)*π*I‖=2*π := by simp [abs_of_pos pi_pos]
  rw [hc]
  have ht : (|2*π*t|+2)^(-(3/2:ℝ)) ≤ decayMajorant t := by
    dsimp [decayMajorant]
    apply Real.rpow_le_rpow_of_nonpos (by positivity)
    · rw [abs_mul,abs_mul,abs_of_pos pi_pos]
      norm_num
      nlinarith [abs_nonneg t,pi_gt_three]
    · norm_num
  calc
    _ ≤ (2*π)^n*(D*((q:ℝ)+2)^(1/2:ℝ)*(|2*π*t|+2)^(-(3/2:ℝ))) :=
      mul_le_mul_of_nonneg_left (hb q χ hp σ (2*π*t) hσ hσ2) (by positivity)
    _ ≤ (2*π)^n*(D*((q:ℝ)+2)^(1/2:ℝ)*decayMajorant t) := by gcongr
    _ = _ := by ring

lemma logRieszVertical_integrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {σ : ℝ} (hσ : 1≤σ) (hσ2 : σ≤2) (n : ℕ) :
    Integrable (iteratedDeriv n (logRieszVertical χ σ)) := by
  obtain ⟨D,hD,hb⟩ := logRieszVertical_bound n
  exact integrable_of_decay_bound
    ((logRieszVertical_contDiff χ hσ).continuous_iteratedDeriv n (by simp))
    (hb q χ hp σ · hσ hσ2)

lemma logRiesz_mellinInv_bound (n : ℕ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ σ x : ℝ, 1≤σ → σ≤2 → 1<x →
        ‖mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*x^σ/(Real.log x)^n := by
  obtain ⟨D,hD,hb⟩ := logRieszVertical_bound n
  let J : ℝ := ∫ t, decayMajorant t
  refine ⟨D*(|J|+1),by dsimp [J]; positivity,?_⟩
  intro q _ χ hp σ x hσ hσ2 hx
  have hx0 : 0<x := by linarith
  have hlog : 0<Real.log x := Real.log_pos hx
  have hi := logRieszVertical_integrable χ hp hσ hσ2
  have hg := logRieszVertical_contDiff χ hσ
  have hb' : (∫ t, ‖iteratedDeriv n (logRieszVertical χ σ) t‖) ≤ D*((q:ℝ)+2)^(1/2:ℝ)*J :=
    integral_norm_le_of_decay_bound (hg.continuous_iteratedDeriv n (by simp)) (hb q χ hp σ · hσ hσ2)
  have hf := fourierInv_decay hg hi n hb' (u:=Real.log x) (by rwa [abs_of_pos hlog])
  rw [mellinInv_eq_fourierInv σ _ (one_div_pos.mpr hx0),norm_smul,
    Complex.norm_cpow_eq_rpow_re_of_pos (one_div_pos.mpr hx0)]
  have he : -(Real.log (1/x))=Real.log x := by simp
  rw [he]
  change (1/x)^(-σ)*‖𝓕⁻ (logRieszVertical χ σ) (Real.log x)‖ ≤ _
  rw [one_div,Real.inv_rpow hx0.le,←Real.rpow_neg hx0.le,neg_neg]
  have hJ : J ≤ |J|+1 := by linarith [le_abs_self J]
  have hfac : 0≤ D*((q:ℝ)+2)^(1/2:ℝ) := by positivity
  calc
    _ ≤ x^σ*(D*((q:ℝ)+2)^(1/2:ℝ)*J/|Real.log x|^n) := mul_le_mul_of_nonneg_left hf (by positivity)
    _ ≤ x^σ*(D*((q:ℝ)+2)^(1/2:ℝ)*(|J|+1)/(Real.log x)^n) := by
      rw [abs_of_pos hlog]
      gcongr
    _ = _ := by ring

open Complex Real Set MeasureTheory Filter Topology

noncomputable def primeCoefficients {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)

noncomputable def characterMain {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ := by
  classical
  exact if χ=1 then 1 else 0

lemma characterMain_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) : ‖characterMain χ‖≤1 := by
  unfold characterMain
  split_ifs <;> norm_num

lemma primeCoefficients_summable {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (primeCoefficients χ) s := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs

lemma primeCoefficients_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖primeCoefficients χ n‖≤Real.log n := by
  rw [primeCoefficients,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact (mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)).trans
    ArithmeticFunction.vonMangoldt_le_log

lemma primeRiesz_identity {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1<s.re) :
    LSeries (primeCoefficients χ) s/(s*(s+1))=
      logRiesz (poleRemovedL χ) s+characterMain χ*(1/((s-1)*s*(s+1))) := by
  have he := primeLogDerivativeRegular_eq χ hs
  change primeLogDerivativeRegular χ s=LSeries (primeCoefficients χ) s-_ at he
  have hlog : logRiesz (poleRemovedL χ) s=primeLogDerivativeRegular χ s/(s*(s+1)) := rfl
  have hs0 : s≠0 := by intro h; simp [h] at hs; norm_num at hs
  have hs1 : s-1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hs2 : s+1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [hlog,he,characterMain]
  split_ifs <;> field_simp <;> ring

lemma logRiesz_verticalIntegrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {σ : ℝ} (hσ : 1≤σ) (hσ2 : σ≤2) :
    VerticalIntegrable (logRiesz (poleRemovedL χ)) σ := by
  have hπ : (2*π:ℝ)≠0 := by positivity
  have hi := (logRieszVertical_integrable χ hp hσ hσ2 0).comp_mul_left' (inv_ne_zero hπ)
  simp only [iteratedDeriv_zero] at hi
  have he : (fun t : ℝ => logRieszVertical χ σ ((2*π)⁻¹*t))=
      (fun t : ℝ => logRiesz (poleRemovedL χ) (σ+t*I)) := by
    ext t
    dsimp [logRieszVertical]
    congr 1
    push_cast
    field_simp
  rwa [he] at hi

lemma primeRiesz_mellinInv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {σ x : ℝ} (hσ : 1<σ) (hσ2 : σ≤2) (hx : 0<x) :
    mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)=
      rieszSum (primeCoefficients χ) x-characterMain χ*poleRieszKernel (1/x) := by
  have he : rieszSum (primeCoefficients χ) x=
      mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)+characterMain χ*poleRieszKernel (1/x) := by
    rw [←rieszSum_mellinInv hσ.le hx _ (primeCoefficients_summable χ (by simpa using hσ))]
    calc
      _ = mellinInv σ (fun s => logRiesz (poleRemovedL χ) s+
          characterMain χ*(1/((s-1)*s*(s+1)))) (1/x) := by
        unfold mellinInv
        congr 1
        apply integral_congr_ae
        filter_upwards [] with t
        rw [primeRiesz_identity χ (by simpa using hσ)]
      _ = mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)+
          mellinInv σ (fun s => characterMain χ*(1/((s-1)*s*(s+1)))) (1/x) :=
        mellinInv_add_of_verticalIntegrable (one_div_pos.mpr hx)
          (logRiesz_verticalIntegrable χ hp hσ.le hσ2) ((poleRiesz_verticalIntegrable hσ).const_mul _)
      _ = _ := by rw [mellinInv_const_mul,poleRiesz_mellinInv hσ (one_div_pos.mpr hx)]
  linear_combination -he

lemma primeRiesz_error_bound (n : ℕ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ σ x : ℝ, 1<σ → σ≤2 → 1<x →
        ‖rieszSum (primeCoefficients χ) x-characterMain χ*(x:ℂ)/2‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*x^σ/(Real.log x)^n+1 := by
  obtain ⟨D,hD,hb⟩ := logRiesz_mellinInv_bound n
  refine ⟨D,hD,?_⟩
  intro q _ χ hp σ x hσ hσ2 hx
  have he := primeRiesz_mellinInv χ hp hσ hσ2 (by linarith : 0<x)
  rw [poleRieszKernel_inv hx.le] at he
  have he' : rieszSum (primeCoefficients χ) x-characterMain χ*(x:ℂ)/2=
      mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)+characterMain χ*((-1+1/(2*x):ℝ):ℂ) := by
    push_cast at he ⊢
    linear_combination -he
  rw [he']
  apply (norm_add_le _ _).trans
  apply add_le_add (hb q χ hp σ x hσ.le hσ2 hx)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  have ht : |-1+1/(2*x)|≤1 := by
    rw [abs_le]
    have hx0 : 0<x := by linarith
    have ht0 : 0≤1/(2*x) := by positivity
    have ht1 : 1/(2*x)≤1 := (div_le_one (by positivity)).mpr (by linarith)
    constructor <;> linarith
  exact (mul_le_mul (characterMain_norm_le χ) ht (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

open Complex Real Set MeasureTheory Filter Topology

noncomputable def weightedPrefix (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n∈Finset.Ioc 0 ⌊x⌋₊, ((x-(n:ℝ):ℝ):ℂ)*a n

lemma weightedPrefix_difference {x h : ℝ} (hh : 0≤h) (a : ℕ → ℂ) :
    weightedPrefix a (x+h)-weightedPrefix a x=
      (h:ℂ)*(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)+
      ∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n := by
  classical
  have hfloor : ⌊x⌋₊≤⌊x+h⌋₊ := Nat.floor_mono (by linarith)
  have he : Finset.Ioc 0 ⌊x+h⌋₊=Finset.Ioc 0 ⌊x⌋₊ ∪ Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊ := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_union]
    omega
  have hd : Disjoint (Finset.Ioc 0 ⌊x⌋₊) (Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊) := by
    rw [Finset.disjoint_left]
    intro n h₁ h₂
    simp only [Finset.mem_Ioc] at h₁ h₂
    omega
  unfold weightedPrefix
  rw [he,Finset.sum_union hd]
  have hs : (∑ n∈Finset.Ioc 0 ⌊x⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n)=
      (h:ℂ)*(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)+
      ∑ n∈Finset.Ioc 0 ⌊x⌋₊, ((x-(n:ℝ):ℝ):ℂ)*a n := by
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    push_cast
    ring
  rw [hs]
  ring

lemma weightedPrefix_tail_bound {x h L : ℝ} (hx : 0≤x) (hh : 0≤h) (hL : 0≤L)
    (a : ℕ → ℂ) (ha : ∀ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ‖a n‖≤L) :
    ‖∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n‖ ≤ (h+1)*(h*L) := by
  have hfloor : ⌊x⌋₊≤⌊x+h⌋₊ := Nat.floor_mono (by linarith)
  have hn (n : ℕ) (hn : n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊) :
      0≤x+h-(n:ℝ) ∧ x+h-(n:ℝ)≤h := by
    obtain ⟨h₁,h₂⟩ := Finset.mem_Ioc.mp hn
    have hlo : x<(n:ℝ) := by
      have hn' : (⌊x⌋₊:ℝ)+1≤n := by exact_mod_cast h₁
      linarith [Nat.lt_floor_add_one x]
    have hup : (n:ℝ)≤x+h := (Nat.le_floor_iff (by linarith)).mp h₂
    constructor <;> linarith
  have hc : ((Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊).card:ℝ) ≤ h+1 := by
    rw [Nat.card_Ioc,Nat.cast_sub hfloor]
    have hlo := Nat.lt_floor_add_one x
    have hup := Nat.floor_le (by linarith : 0≤x+h)
    linarith
  calc
    _ ≤ ∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ‖((x+h-(n:ℝ):ℝ):ℂ)*a n‖ := norm_sum_le _ _
    _ ≤ ∑ _n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, h*L := by
      apply Finset.sum_le_sum
      intro n hn'
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hn n hn').1]
      exact mul_le_mul (hn n hn').2 (ha n hn') (norm_nonneg _) hh
    _ = ((Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊).card:ℝ)*(h*L) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (mul_nonneg hh hL)

lemma prefix_unsmoothing {x h L : ℝ} (hx : 0≤x) (hh : 0<h) (hL : 0≤L)
    (a : ℕ → ℂ) (δ : ℂ) (ha : ∀ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ‖a n‖≤L) :
    ‖(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ)‖ ≤
      (‖weightedPrefix a (x+h)-δ*((x+h:ℝ):ℂ)^2/2‖+
        ‖weightedPrefix a x-δ*(x:ℂ)^2/2‖)/h+(h+1)*L+‖δ‖*h/2 := by
  let T := ∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n
  let E (y : ℝ) := weightedPrefix a y-δ*(y:ℂ)^2/2
  have he : (h:ℂ)*((∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ))=
      (E (x+h)-E x)-T+δ*(h:ℂ)^2/2 := by
    have hd := weightedPrefix_difference (x:=x) hh.le a
    change weightedPrefix a (x+h)-weightedPrefix a x = _+T at hd
    dsimp [E]
    push_cast
    linear_combination -hd
  have hn : h*‖(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ)‖ ≤
      (‖E (x+h)‖+‖E x‖)+((h+1)*(h*L))+‖δ‖*h^2/2 := by
    calc
      _ = ‖(h:ℂ)*((∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ))‖ := by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
      _ = ‖(E (x+h)-E x)-T+δ*(h:ℂ)^2/2‖ := congrArg norm he
      _ ≤ ‖E (x+h)-E x‖+‖T‖+‖δ*(h:ℂ)^2/2‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ (‖E (x+h)‖+‖E x‖)+((h+1)*(h*L))+‖δ‖*h^2/2 := by
        have hT : ‖T‖≤(h+1)*(h*L) := weightedPrefix_tail_bound hx hh.le hL a ha
        have hδ : ‖δ*(h:ℂ)^2/2‖=‖δ‖*h^2/2 := by
          simp [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
        rw [hδ]
        exact add_le_add (add_le_add (norm_sub_le _ _) hT) le_rfl
  have hd : h*((‖E (x+h)‖+‖E x‖)/h+(h+1)*L+‖δ‖*h/2)=
      (‖E (x+h)‖+‖E x‖)+((h+1)*(h*L))+‖δ‖*h^2/2 := by field_simp
  dsimp [E] at hn hd
  apply (mul_le_mul_iff_left₀ hh).mp
  rw [mul_comm _ h, mul_comm _ h, hd]
  exact hn

open Complex Real Set MeasureTheory Filter Topology

lemma weightedPrefix_eq_mul_rieszSum (a : ℕ → ℂ) {x : ℝ} (hx : 0<x) :
    weightedPrefix a x=(x:ℂ)*rieszSum a x := by
  unfold weightedPrefix rieszSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hx0 : (x:ℂ)≠0 := by exact_mod_cast hx.ne'
  push_cast
  field_simp

lemma rpow_one_add_inv_log {x : ℝ} (hx : 1<x) :
    x^(1+1/Real.log x)=Real.exp 1*x := by
  have hx0 : 0<x := by linarith
  have hlog : Real.log x≠0 := (Real.log_pos hx).ne'
  rw [Real.rpow_add hx0,Real.rpow_one,Real.rpow_def_of_pos hx0]
  rw [mul_one_div_cancel hlog]
  ring

lemma primeWeighted_error_bound (a : ℝ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ x : ℝ, 1<x → 1≤Real.log x →
        ‖weightedPrefix (primeCoefficients χ) x-characterMain χ*(x:ℂ)^2/2‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*x^2*(Real.log x)^(-a)+x := by
  obtain ⟨D,hD,hb⟩ := primeRiesz_error_bound ⌈a⌉₊
  refine ⟨D*Real.exp 1,by positivity,?_⟩
  intro q _ χ hp x hx hL
  have hx0 : 0<x := by linarith
  have hlog : 0<Real.log x := Real.log_pos hx
  have hσ : 1<1+1/Real.log x := by linarith [one_div_pos.mpr hlog]
  have hσ2 : 1+1/Real.log x≤2 := by
    have : 1/Real.log x≤1 := (div_le_one hlog).mpr hL
    linarith
  have he : weightedPrefix (primeCoefficients χ) x-characterMain χ*(x:ℂ)^2/2=
      (x:ℂ)*(rieszSum (primeCoefficients χ) x-characterMain χ*(x:ℂ)/2) := by
    rw [weightedPrefix_eq_mul_rieszSum _ hx0]
    ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx0]
  calc
    _ ≤ x*(D*((q:ℝ)+2)^(1/2:ℝ)*x^(1+1/Real.log x)/(Real.log x)^⌈a⌉₊+1) :=
      mul_le_mul_of_nonneg_left (hb q χ hp _ x hσ hσ2 hx) hx0.le
    _ = D*Real.exp 1*((q:ℝ)+2)^(1/2:ℝ)*x^2*(Real.log x)^(-(⌈a⌉₊:ℝ))+x := by
      rw [rpow_one_add_inv_log hx,Real.rpow_neg hlog.le,Real.rpow_natCast]
      ring
    _ ≤ _ := by
      have hn : a≤(⌈a⌉₊:ℝ) := Nat.le_ceil a
      gcongr

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_RieszDecay

section File_OpenAIPrimeGaps_Main

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace OAI

namespace LargePrimeGaps

open Complex Real Set MeasureTheory Filter Topology

open Complex Filter Topology

open Complex Filter Topology MeasureTheory

open scoped FourierTransform

open Complex Real Set MeasureTheory Filter Topology

open Complex Real Set MeasureTheory Filter Topology

open Complex Real Set MeasureTheory Filter Topology

open scoped FourierTransform

open Complex Real Set MeasureTheory Filter Topology

open Complex Real Set MeasureTheory Filter Topology

open Complex Real Set MeasureTheory Filter Topology

lemma primeCharacterError_log_bound (A B : ℝ) (hA : 0<A) (hB : 0<B) :
    ∃ M : ℝ, 0<M ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ x : ℝ, 2≤x → 1≤Real.log x → (Real.log x)^(2*A+2)≤x →
        (q:ℝ)≤(Real.log x)^B →
        ‖primeCharacterError x χ‖≤M*x*(Real.log x)^(-A) := by
  obtain ⟨D,hD,hb⟩ := primeWeighted_error_bound (B+2*A+2)
  refine ⟨15*D+8,by positivity,?_⟩
  intro q _ χ hp x hx hL hpower hq
  let L := Real.log x
  let K := A+2
  let a := B+2*A+2
  let Q := ((q:ℝ)+2)^(1/2:ℝ)
  let h := x/L^K
  have hx0 : 0<x := by linarith
  have hx1 : 1<x := by linarith
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hK : 0<K := by dsimp [K]; linarith
  have ha : 0<a := by dsimp [a]; linarith
  have hpK : 0<L^K := Real.rpow_pos_of_pos hL0 _
  have hh0 : 0<h := div_pos hx0 hpK
  have hK1 : 1≤L^K := Real.one_le_rpow hL hK.le
  have hhx : h≤x := (div_le_self hx0.le hK1)
  have hKh : L^K≤x := by
    apply (Real.rpow_le_rpow_of_exponent_le hL (show K≤2*A+2 by dsimp [K]; linarith)).trans
    exact hpower
  have hh1 : 1≤h := (le_div_iff₀ hpK).mpr (by simpa using hKh)
  have hyx : x≤x+h := by linarith
  have hy : 1<x+h := by linarith
  have hy2 : x+h≤2*x := by linarith
  have hLy : L≤Real.log (x+h) := Real.log_le_log hx0 hyx
  have hLy1 : 1≤Real.log (x+h) := hL.trans hLy
  have hLy2 : Real.log (x+h)≤2*L := by
    calc
      _ ≤ Real.log (x^2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; rfl
  have hQ0 : 0≤Q := by dsimp [Q]; positivity
  have hQ : Q≤3*L^B := by
    have hq2 : 1≤(q:ℝ)+2 := by have := Nat.cast_nonneg (α:=ℝ) q; linarith
    have hqpow : Q≤(q:ℝ)+2 := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hq2 (show (1/2:ℝ)≤1 by norm_num)
    have hLB : 1≤L^B := Real.one_le_rpow hL hB.le
    linarith
  let E (y : ℝ) := ‖weightedPrefix (primeCoefficients χ) y-characterMain χ*(y:ℂ)^2/2‖
  have hEx : E x≤D*Q*x^2*L^(-a)+x := hb q χ hp x hx1 hL
  have hEy : E (x+h)≤4*D*Q*x^2*L^(-a)+2*x := by
    calc
      _ ≤ D*Q*(x+h)^2*(Real.log (x+h))^(-a)+(x+h) := hb q χ hp (x+h) hy hLy1
      _ ≤ D*Q*(2*x)^2*L^(-a)+2*x := by
        apply add_le_add _ hy2
        apply mul_le_mul _ (Real.rpow_le_rpow_of_nonpos hL0 hLy (neg_nonpos.mpr ha.le)) (by positivity) (by positivity)
        gcongr
      _ = _ := by ring
  have hcoeff (n : ℕ) (hn : n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊) :
      ‖primeCoefficients χ n‖≤2*L := by
    have hn0 : 0<(n:ℝ) := by exact_mod_cast (show 0<n by have := (Finset.mem_Ioc.mp hn).1; omega)
    have hnx : (n:ℝ)≤x+h := (Nat.le_floor_iff (by linarith : 0≤x+h)).mp (Finset.mem_Ioc.mp hn).2
    exact (primeCoefficients_norm_le χ n).trans ((Real.log_le_log hn0 hnx).trans hLy2)
  have heq : primeCharacterError x χ=
      (∑ n∈Finset.Ioc 0 ⌊x⌋₊, primeCoefficients χ n)-characterMain χ*(x:ℂ) := by
    classical
    simp only [primeCharacterError,primeCharacterPrefix,primeCoefficients,characterMain]
    split_ifs <;> simp
  rw [heq]
  have hu := prefix_unsmoothing hx0.le hh0 (show 0≤2*L by positivity)
    (primeCoefficients χ) (characterMain χ) hcoeff
  change _≤(E (x+h)+E x)/h+(h+1)*(2*L)+‖characterMain χ‖*h/2 at hu
  have hδ : ‖characterMain χ‖*h/2≤h := by
    have := mul_le_mul_of_nonneg_right (characterMain_norm_le χ) hh0.le
    linarith
  have htail : (h+1)*(2*L)≤4*h*L := by nlinarith
  have herr : (E (x+h)+E x)/h ≤ 15*D*x*L^(-A)+3*x*L^(-A) := by
    calc
      _ ≤ (5*D*Q*x^2*L^(-a)+3*x)/h := by
        apply div_le_div_of_nonneg_right _ hh0.le
        linarith
      _ ≤ (5*D*(3*L^B)*x^2*L^(-a)+3*x)/h := by gcongr
      _ = (15*D*L^B*x^2*L^(-a)+3*x)/h := by ring
      _ = 15*D*x*L^(-A)+3*L^K := by
        dsimp [h]
        rw [div_eq_mul_inv,inv_div]
        have hr : L^B*L^(-a)*L^K=L^(-A) := by
          rw [←Real.rpow_add hL0,←Real.rpow_add hL0]
          congr 1
          dsimp [a,K]
          ring
        field_simp
        linear_combination 15*D*x*hr
      _ ≤ _ := by
        have ht : L^K≤x*L^(-A) := by
          calc
            _ = L^(2*A+2)*L^(-A) := by rw [←Real.rpow_add hL0]; congr 1; dsimp [K]; ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hpower (by positivity)
        nlinarith [ht]
  have hsmall : h≤x*L^(-A) := by
    dsimp [h]
    rw [div_eq_mul_inv,←Real.rpow_neg hL0.le]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (show -K≤-A by dsimp [K]; linarith)) hx0.le
  have htail' : 4*h*L≤4*x*L^(-A) := by
    calc
      _ = 4*x*L^(1-K) := by
        dsimp [h]
        rw [div_eq_mul_inv,Real.rpow_sub hL0,Real.rpow_one]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL (show 1-K≤-A by dsimp [K]; linarith)) (by positivity)
  calc
    _ ≤ (E (x+h)+E x)/h+(h+1)*(2*L)+‖characterMain χ‖*h/2 := hu
    _ ≤ (15*D*x*L^(-A)+3*x*L^(-A))+4*x*L^(-A)+x*L^(-A) :=
      add_le_add (add_le_add herr (htail.trans htail')) (hδ.trans hsmall)
    _ = _ := by ring

theorem siegelWalfisz : SiegelWalfisz := by
  intro A B hA hB
  obtain ⟨M,hM,hb⟩ := primeCharacterError_log_bound A B hA hB
  have hevent : ∀ᶠ x : ℝ in atTop, 2≤x ∧ 1≤Real.log x ∧ (Real.log x)^(2*A+2)≤x := by
    filter_upwards [eventually_ge_atTop (2:ℝ),eventually_ge_atTop (Real.exp 1),
      eventually_log_rpow_le_rpow (2*A+2) (by norm_num : (0:ℝ)<1)] with x hx hex hp
    refine ⟨hx,?_,by simpa only [Real.rpow_one] using hp⟩
    rw [←Real.log_exp (1:ℝ)]
    exact Real.log_le_log (Real.exp_pos _) hex
  obtain ⟨x₀,hx₀⟩ := eventually_atTop.mp hevent
  refine ⟨M,hM,max x₀ 2,by have := le_max_right x₀ (2:ℝ); linarith,?_⟩
  intro x hx d hd hdlog χ hχ
  let : NeZero d := ⟨ne_of_gt hd⟩
  obtain ⟨hx2,hlog,hpower⟩ := hx₀ x ((le_max_left _ _).trans hx)
  exact hb d χ hχ x hx2 hlog hpower hdlog

theorem bombieriVinogradov : BombieriVinogradov :=
  bombieriVinogradov_of_siegelWalfisz siegelWalfisz

theorem main : ∀ C : ℝ, 0 < C →
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℝ) ≤ ((largeGapIndices C N).card : ℝ) :=
  index_density_of_bombieriVinogradov bombieriVinogradov

end LargePrimeGaps

end OAI

end File_OpenAIPrimeGaps_Main

