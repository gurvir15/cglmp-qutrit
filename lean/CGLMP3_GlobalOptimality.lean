import Mathlib.Tactic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Global optimality of qutrit CGLMP measurements at the fixed maximally entangled state

The final theorem CGLMP3SOS.full_global_optimality states the universal
Born-probability upper bound over all unitary qutrit measurement bases and
the existence of an attaining quadruple. It has no analytic certificate
or angular-budget argument. The upper bound is proved by an exact tracial
sum-of-squares certificate for four cubic unitaries. Every finite arithmetic
and word-reduction table is checked by Lean's kernel.

Lean 4.24.0 / Mathlib v4.24.0. See verification.log for the source hash,
compiler exit status, theorem type, and complete axiom audit.
-/


namespace CGLMP3Concrete
set_option maxHeartbeats 0
noncomputable section
open scoped Matrix
abbrev M3 := Matrix (Fin 3) (Fin 3) ℂ

def quarter (s : ℝ) : M3 :=
  let a : ℂ := ⟨(3+s)/6, (1+s)/6⟩
  let b : ℂ := ⟨(3-s)/6, (1-s)/6⟩
  let c : ℂ := ⟨0, -1/3⟩
  ![![a,c,b], ![b,a,c], ![c,b,a]]

def half (s : ℝ) : M3 :=
  let a : ℂ := ⟨1/3, s/3⟩
  let b : ℂ := ⟨1/3, 0⟩
  let c : ℂ := ⟨1/3, -s/3⟩
  ![![a,c,b], ![b,a,c], ![c,b,a]]

def shift : M3 := ![![0,1,0], ![0,0,1], ![1,0,0]]

theorem quarter_unitary (s : ℝ) (hs : s^2=3) :
    quarter s * (quarter s)ᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [quarter, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im] <;> nlinarith [hs]

theorem quarter_square (s : ℝ) (hs : s^2=3) :
    quarter s * quarter s = half s := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [quarter, half, Matrix.mul_apply, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im] <;> nlinarith [hs]

theorem half_square (s : ℝ) (hs : s^2=3) : half s * half s = shift := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [half, shift, Matrix.mul_apply, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im] <;> nlinarith [hs]

theorem quarter_fourth (s : ℝ) (hs : s^2=3) : (quarter s)^4 = shift := by
  calc
    (quarter s)^4 = (quarter s * quarter s) * (quarter s * quarter s) := by noncomm_ring
    _ = half s * half s := by rw [quarter_square s hs]
    _ = shift := half_square s hs

/-- Modular displacement [a-b]_3, with ordinary natural remainder. -/
def displacement (a b : Fin 3) : ℝ := ((a.val + 3 - b.val) % 3 : ℕ)

/-- Directed physical overlap cost, with the maximally entangled 1/3 factor. -/
noncomputable def cost (U : M3) : ℝ :=
  (∑ a : Fin 3, ∑ b : Fin 3, displacement a b * Complex.normSq (U a b)) / 3

theorem quarter_cost (s : ℝ) (hs : s^2=3) : cost (quarter s) = (6-2*s)/9 := by
  norm_num [cost, quarter, displacement, Fin.sum_univ_succ, Complex.normSq_apply]
  nlinarith [hs]

noncomputable def Q : M3 := quarter (Real.sqrt 3)

theorem sqrt_three_sq : (Real.sqrt (3 : ℝ))^2=3 := Real.sq_sqrt (by norm_num)

theorem Q_unitary : Q ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  exact quarter_unitary _ sqrt_three_sq

theorem Q_fourth : Q^4=shift := quarter_fourth _ sqrt_three_sq

theorem Q_cost : cost Q = (2 : ℝ)/3 * (1 - 1/Real.sqrt 3) := by
  have hp : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  rw [Q, quarter_cost _ sqrt_three_sq]
  field_simp
  nlinarith [sqrt_three_sq]

theorem equal_step_attainment :
    Q ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
    Q * Q * Q * Q = shift ∧
    4 - (cost Q + cost Q + cost Q + cost Q) =
      (4 : ℝ)/3 + 8/(3*Real.sqrt 3) := by
  refine ⟨Q_unitary, ?_, ?_⟩
  · simpa [pow_succ] using Q_fourth
  · rw [Q_cost]
    ring

#print axioms equal_step_attainment
end
end CGLMP3Concrete


namespace CGLMP3Physical
noncomputable section
open scoped Matrix
abbrev M3 := Matrix (Fin 3) (Fin 3) ℂ
def shift : M3 := ![![0,1,0], ![0,0,1], ![1,0,0]]
def displacement (a b : Fin 3) : ℝ := ((a.val+3-b.val)%3 : ℕ)
def lastDisplacement (a b : Fin 3) : ℝ := ((b.val+5-a.val)%3 : ℕ)
def cost (U : M3) : ℝ :=
  (∑ a : Fin 3, ∑ b : Fin 3, displacement a b * Complex.normSq (U a b))/3

/-- Born probabilities on |Phi_3>, with effective Alice basis E=conj(A).
The normalized amplitude is (E^dagger F)_ab / sqrt(3). -/
def probability (E F : M3) (a b : Fin 3) : ℝ :=
  Complex.normSq ((Eᴴ * F) a b)/3

def conjugateBasis (A : M3) : M3 := fun i j => star (A i j)

/-- Squared Born amplitude on the explicitly normalized bipartite qutrit state. -/
def bornProbability (A B : M3) (a b : Fin 3) : ℝ :=
  Complex.normSq (∑ j : Fin 3, A j a * B j b)/3

theorem born_eq_effective (A B : M3) (a b : Fin 3) :
    bornProbability A B a b = probability (conjugateBasis A) B a b := by
  simp [bornProbability, probability, conjugateBasis, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

theorem conjugateBasis_unitary (A : M3)
    (ha : A ∈ Matrix.unitaryGroup (Fin 3) ℂ) :
    conjugateBasis A ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change conjugateBasis A * (conjugateBasis A)ᴴ = 1
  have hu := Matrix.mem_unitaryGroup_iff.mp ha
  change A * Aᴴ = 1 at hu
  ext i j
  have h := congrArg (fun M : M3 => star (M i j)) hu
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, conjugateBasis, Matrix.one_apply] using h

theorem probability_nonneg (E F : M3) (a b : Fin 3) :
    0 ≤ probability E F a b := div_nonneg (Complex.normSq_nonneg _) (by norm_num)

theorem normSq_row (U : M3) (hu : U * Uᴴ = 1) (a : Fin 3) :
    (∑ b : Fin 3, Complex.normSq (U a b)) = 1 := by
  have h := congrArg (fun M : M3 => (M a a).re) hu
  simpa [Matrix.mul_apply, Complex.mul_re, Complex.normSq_apply] using h

theorem probability_normalized (E F : M3)
    (hE : E ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (hF : F ∈ Matrix.unitaryGroup (Fin 3) ℂ) :
    (∑ a : Fin 3, ∑ b : Fin 3, probability E F a b) = 1 := by
  have hU : (Eᴴ*F) * (Eᴴ*F)ᴴ = 1 := by
    have he := Matrix.mem_unitaryGroup_iff'.mp hE
    have hf := Matrix.mem_unitaryGroup_iff.mp hF
    change Eᴴ * E = 1 at he
    change F * Fᴴ = 1 at hf
    calc
      (Eᴴ*F) * (Eᴴ*F)ᴴ = Eᴴ * (F * Fᴴ) * E := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
        noncomm_ring
      _ = 1 := by rw [hf]; simpa using he
  simp only [probability, ← Finset.sum_div, normSq_row _ hU]
  norm_num

/-- The modular CGLMP expression, with all four terms evaluated on joint Born probabilities. -/
def bellCost (E₀ E₁ F₀ F₁ : M3) : ℝ :=
  (∑ a : Fin 3, ∑ b : Fin 3, displacement a b * probability E₀ F₀ a b) +
  (∑ a : Fin 3, ∑ b : Fin 3, displacement b a * probability E₁ F₀ a b) +
  (∑ a : Fin 3, ∑ b : Fin 3, displacement a b * probability E₁ F₁ a b) +
  (∑ a : Fin 3, ∑ b : Fin 3, lastDisplacement a b * probability E₀ F₁ a b)

theorem direct_cost (E F : M3) :
    (∑ a : Fin 3, ∑ b : Fin 3, displacement a b * probability E F a b) = cost (Eᴴ*F) := by
  simp only [cost, probability, Finset.sum_div, mul_div_assoc]

theorem reverse_probability (E F : M3) (a b : Fin 3) :
    probability E F a b = probability F E b a := by
  have h : Fᴴ*E = (Eᴴ*F)ᴴ := by simp
  simp [probability, h, Matrix.conjTranspose_apply]

theorem reverse_cost (E F : M3) :
    (∑ a : Fin 3, ∑ b : Fin 3, displacement b a * probability E F a b) = cost (Fᴴ*E) := by
  simp_rw [reverse_probability E F]
  rw [Finset.sum_comm]
  exact direct_cost F E

theorem shifted_cost (E F : M3) :
    (∑ a : Fin 3, ∑ b : Fin 3, lastDisplacement a b * probability E F a b) =
      cost (Fᴴ*E*shift) := by
  have h : Fᴴ*E = (Eᴴ*F)ᴴ := by simp
  simp only [probability]
  rw [h]
  generalize Eᴴ * F = W
  norm_num [cost, lastDisplacement, displacement, shift,
    Fin.sum_univ_succ, Matrix.mul_apply, Matrix.conjTranspose_apply]
  ring

theorem physical_cost_factorization (E₀ E₁ F₀ F₁ : M3) :
    bellCost E₀ E₁ F₀ F₁ =
      cost (E₀ᴴ*F₀) + cost (F₀ᴴ*E₁) + cost (E₁ᴴ*F₁) + cost (F₁ᴴ*E₀*shift) := by
  unfold bellCost
  rw [direct_cost, reverse_cost, direct_cost, shifted_cost]

#print axioms physical_cost_factorization
#print axioms probability_normalized
end
end CGLMP3Physical


namespace CGLMP3Trace
noncomputable section
open scoped Matrix
set_option maxHeartbeats 0
abbrev M3 := Matrix (Fin 3) (Fin 3) ℂ
def clock (s : ℝ) : M3 :=
  ![![1,0,0], ![0,⟨-1/2,s/2⟩,0], ![0,0,⟨-1/2,-s/2⟩]]
def shift : M3 := ![![0,1,0], ![0,0,1], ![1,0,0]]
def center (s : ℝ) : M3 :=
  let c : ℂ := ⟨-1/2,-s/2⟩
  ![![c,0,0], ![0,c,0], ![0,0,c]]
def K (s : ℝ) (U : M3) : M3 := clock s * U * (clock s)ᴴ * Uᴴ

theorem clock_shift (s : ℝ) (hs : s^2=3) :
    clock s * shift = center s * shift * clock s := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [clock, shift, center, Matrix.scalar, Matrix.mul_apply,
      Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im] <;> nlinarith [hs]

theorem clock_unitary (s : ℝ) (hs : s^2=3) : clock s * (clock s)ᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [clock, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im] <;> nlinarith [hs]

def displacement (a b : Fin 3) : ℝ := ((a.val+3-b.val)%3 : ℕ)
def cost (U : M3) : ℝ :=
  (∑ a : Fin 3, ∑ b : Fin 3, displacement a b * Complex.normSq (U a b))/3
def mass (U : M3) : ℝ := (∑ a : Fin 3, ∑ b : Fin 3, Complex.normSq (U a b))/3

theorem cost_trace_polynomial (s : ℝ) (hs : s^2=3) (U : M3) :
    cost U = mass U - (Matrix.trace (K s U)).re / 3 -
      s * (Matrix.trace (K s U)).im / 9 := by
  simp [cost, mass, displacement, K, clock, Matrix.trace,
    Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring_nf
  simp only [hs]
  ring

#print axioms clock_shift
#print axioms cost_trace_polynomial
end
end CGLMP3Trace

namespace CGLMP3Integration
noncomputable section
open scoped Matrix
abbrev M3 := Matrix (Fin 3) (Fin 3) ℂ

def ell (K : M3) : ℝ :=
  1 - (Matrix.trace K).re/3 - (Matrix.trace K).im/(3*Real.sqrt 3)

theorem physical_cost_trace (U : M3)
    (hu : U ∈ Matrix.unitaryGroup (Fin 3) ℂ) :
    CGLMP3Physical.cost U = ell (CGLMP3Trace.K (Real.sqrt 3) U) := by
  have hrow := CGLMP3Physical.normSq_row U (Matrix.mem_unitaryGroup_iff.mp hu)
  have hm : CGLMP3Trace.mass U = 1 := by
    simp [CGLMP3Trace.mass, hrow]
  have hpoly := CGLMP3Trace.cost_trace_polynomial (Real.sqrt 3)
    CGLMP3Concrete.sqrt_three_sq U
  change CGLMP3Trace.cost U = _
  rw [hpoly, hm]
  unfold ell
  have hs : (Real.sqrt (3 : ℝ))/9 = 1/(3*Real.sqrt 3) := by
    have hp : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    field_simp
    nlinarith [CGLMP3Concrete.sqrt_three_sq]
  calc
    _ = 1 - (Matrix.trace (CGLMP3Trace.K (Real.sqrt 3) U)).re/3 -
      (Real.sqrt 3/9) * (Matrix.trace (CGLMP3Trace.K (Real.sqrt 3) U)).im := by ring
    _ = _ := by rw [hs]; ring

theorem ell_conjugation (V K : M3)
    (hv : V ∈ Matrix.unitaryGroup (Fin 3) ℂ) : ell (V*K*Vᴴ) = ell K := by
  have hv' := Matrix.mem_unitaryGroup_iff'.mp hv
  change Vᴴ * V = 1 at hv'
  have htr : Matrix.trace (V*K*Vᴴ) = Matrix.trace K := by
    rw [Matrix.trace_mul_cycle, hv']
    simp
  simp [ell, htr]

theorem explicit_measurement_attainment :
    let Q := CGLMP3Concrete.Q
    (1 : M3) ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
    Q^2 ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
    Q ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
    Q^3 ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
    4 - CGLMP3Physical.bellCost 1 (Q^2) Q (Q^3) =
      (4 : ℝ)/3 + 8/(3*Real.sqrt 3) := by
  dsimp only
  let Q := CGLMP3Concrete.Q
  have hu := CGLMP3Concrete.Q_unitary
  have hq := Matrix.mem_unitaryGroup_iff'.mp hu
  change Qᴴ * Q = 1 at hq
  have hq2 : Qᴴ * Q^2 = Q := by
    rw [pow_two, ← Matrix.mul_assoc, hq]
    simp
  have hq3 : (Q^2)ᴴ * Q^3 = Q := by
    simp only [pow_succ, pow_zero, one_mul, Matrix.conjTranspose_mul]
    calc
      (Qᴴ * Qᴴ) * (Q * Q * Q) = Qᴴ * (Qᴴ * Q) * Q * Q := by noncomm_ring
      _ = Q := by rw [hq]; simp [hq]
  have hq4 : (Q^3)ᴴ * 1 * CGLMP3Physical.shift = Q := by
    change (Q^3)ᴴ * 1 * CGLMP3Concrete.shift = Q
    rw [← CGLMP3Concrete.Q_fourth]
    simp only [pow_succ, pow_zero, one_mul, mul_one, Matrix.conjTranspose_mul]
    calc
      (Qᴴ * (Qᴴ * Qᴴ)) * (Q * Q * Q * Q) =
        Qᴴ * Qᴴ * (Qᴴ * Q) * Q * Q * Q := by noncomm_ring
      _ = Q := by rw [hq]; simp [Matrix.mul_assoc, hq]
  refine ⟨one_mem _, pow_mem hu 2, hu, pow_mem hu 3, ?_⟩
  rw [CGLMP3Physical.physical_cost_factorization]
  dsimp only [Q] at hq2 hq3 hq4
  simp only [Matrix.conjTranspose_one, one_mul, hq2, hq3, hq4]
  change 4 - (CGLMP3Concrete.cost Q + CGLMP3Concrete.cost Q +
    CGLMP3Concrete.cost Q + CGLMP3Concrete.cost Q) = _
  rw [CGLMP3Concrete.Q_cost]
  ring

#print axioms physical_cost_trace
#print axioms ell_conjugation
#print axioms explicit_measurement_attainment

/-- The Bell functional evaluated directly on the bipartite Born probabilities. -/
def actualBellValue (A₀ A₁ B₀ B₁ : M3) : ℝ :=
  4 - ((∑ a : Fin 3, ∑ b : Fin 3,
        CGLMP3Physical.displacement a b * CGLMP3Physical.bornProbability A₀ B₀ a b) +
      (∑ a : Fin 3, ∑ b : Fin 3,
        CGLMP3Physical.displacement b a * CGLMP3Physical.bornProbability A₁ B₀ a b) +
      (∑ a : Fin 3, ∑ b : Fin 3,
        CGLMP3Physical.displacement a b * CGLMP3Physical.bornProbability A₁ B₁ a b) +
      (∑ a : Fin 3, ∑ b : Fin 3,
        CGLMP3Physical.lastDisplacement a b * CGLMP3Physical.bornProbability A₀ B₁ a b))

theorem actual_measurement_attainment :
    let Q := CGLMP3Concrete.Q
    let A₀ := CGLMP3Physical.conjugateBasis (1 : M3)
    let A₁ := CGLMP3Physical.conjugateBasis (Q^2)
    A₀ ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
    A₁ ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
    Q ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
    Q^3 ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
    actualBellValue A₀ A₁ Q (Q^3) = (4 : ℝ)/3 + 8/(3*Real.sqrt 3) := by
  dsimp only
  obtain ⟨h0,h1,h2,h3,hval⟩ := explicit_measurement_attainment
  refine ⟨CGLMP3Physical.conjugateBasis_unitary _ h0,
    CGLMP3Physical.conjugateBasis_unitary _ h1, h2, h3, ?_⟩
  have hconj : ∀ A : M3,
      CGLMP3Physical.conjugateBasis (CGLMP3Physical.conjugateBasis A) = A := by
    intro A
    ext i j
    simp [CGLMP3Physical.conjugateBasis]
  simpa only [actualBellValue, CGLMP3Physical.born_eq_effective, hconj,
    CGLMP3Physical.bellCost] using hval

#print axioms actual_measurement_attainment
end
end CGLMP3Integration


namespace CGLMP3Global
noncomputable section
open scoped Matrix
abbrev M3 := Matrix (Fin 3) (Fin 3) ℂ
abbrev U3 := Matrix.unitaryGroup (Fin 3) ℂ
abbrev SU3 := Matrix.specialUnitaryGroup (Fin 3) ℂ
def clock : M3 := CGLMP3Trace.clock (Real.sqrt 3)
def center : M3 := CGLMP3Trace.center (Real.sqrt 3)
def shift : M3 := CGLMP3Physical.shift

theorem clock_unitary : clock ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  exact CGLMP3Trace.clock_unitary _ CGLMP3Concrete.sqrt_three_sq

theorem shift_unitary : shift ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change shift * shiftᴴ = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shift,CGLMP3Physical.shift,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_succ]

def Z : U3 := ⟨clock,clock_unitary⟩
def S : U3 := ⟨shift,shift_unitary⟩

end
end CGLMP3Global


namespace CGLMP3SOS
abbrev Letter := Fin 4 × Fin 3
abbrev Word := List Letter
def addExp (e f : Fin 3) : Fin 3 := ⟨(e.val+f.val)%3, Nat.mod_lt _ (by decide)⟩
def invExp (e : Fin 3) : Fin 3 := ⟨(3-e.val)%3, Nat.mod_lt _ (by decide)⟩
def eval {G : Type*} [Group G] (u : Fin 4 → G) : Word → G
  | [] => 1
  | (g,e)::w => (u g)^e.val * eval u w

theorem pow_addExp {G : Type*} [Group G] (u : G) (hu : u^3=1) (e f : Fin 3) :
    u^(addExp e f).val = u^e.val * u^f.val := by
  have h4 : u^4=u := by rw [show (4 : ℕ)=3+1 by rfl,pow_add,hu]; simp
  rw [← pow_add]
  fin_cases e <;> fin_cases f <;> norm_num [addExp,hu,h4]

theorem pow_invExp {G : Type*} [Group G] (u : G) (hu : u^3=1) (e : Fin 3) :
    u^(invExp e).val = (u^e.val)⁻¹ := by
  have h2 : u^2=u⁻¹ := by
    calc
      u^2 = u^3*u⁻¹ := by group
      _ = u⁻¹ := by rw [hu]; simp
  fin_cases e <;> norm_num [invExp,h2]

def merge (a : Letter) (w : Word) : Word :=
  if a.2=0 then w else match w with
  | [] => [a]
  | b::rest => if a.1=b.1 then
      let e := addExp a.2 b.2
      if e=0 then rest else (a.1,e)::rest
    else a::w

theorem eval_merge {G : Type*} [Group G] (u : Fin 4 → G)
    (hu : ∀ g, (u g)^3=1) (a : Letter) (w : Word) :
    eval u (merge a w) = (u a.1)^a.2.val * eval u w := by
  rcases a with ⟨g,e⟩
  by_cases he : e=0
  · simp [merge,he,eval]
  · cases w with
    | nil => simp [merge,he,eval]
    | cons b rest =>
      rcases b with ⟨h,f⟩
      by_cases hg : g=h
      · subst h
        by_cases hz : addExp e f=0
        · have hp := pow_addExp (u g) (hu g) e f
          rw [hz] at hp
          simp only [Fin.val_zero,pow_zero] at hp
          simp [merge,he,hz,eval,←mul_assoc,←hp]
        · simp only [merge,he,ite_false,ite_true,hz,eval]
          rw [pow_addExp _ (hu g),mul_assoc]
      · simp [merge,he,hg,eval]

def reduce : Word → Word
  | [] => []
  | a::w => merge a (reduce w)

theorem eval_reduce {G : Type*} [Group G] (u : Fin 4 → G)
    (hu : ∀ g, (u g)^3=1) (w : Word) : eval u (reduce w)=eval u w := by
  induction w with
  | nil => rfl
  | cons a w ih => rw [reduce,eval_merge u hu,ih]; rfl

theorem eval_append {G : Type*} [Group G] (u : Fin 4 → G) (a b : Word) :
    eval u (a++b)=eval u a * eval u b := by
  induction a with
  | nil => simp [eval]
  | cons a w ih => simp [eval,ih,mul_assoc]

def inverseWord (w : Word) : Word := w.reverse.map (fun a => (a.1,invExp a.2))

theorem eval_inverseWord {G : Type*} [Group G] (u : Fin 4 → G)
    (hu : ∀ g, (u g)^3=1) (w : Word) : eval u (inverseWord w)=(eval u w)⁻¹ := by
  induction w with
  | nil => simp [inverseWord,eval]
  | cons a w ih =>
    simp only [inverseWord,List.reverse_cons,List.map_append,List.map_cons,List.map_nil]
    rw [eval_append]
    change eval u (inverseWord w) * ((u a.1)^(invExp a.2).val * 1) = _
    rw [ih,pow_invExp _ (hu a.1)]
    simp [eval,mul_inv_rev]

def rotateAt (w : Word) (k : ℕ) : Word := w.drop k ++ w.take k

theorem trace_rotate {G : Type*} [Group G] (u : Fin 4 → G)
    (τ : G → ℂ) (hτ : ∀ a b, τ (a*b)=τ (b*a)) (w : Word) (k : ℕ) :
    τ (eval u (rotateAt w k))=τ (eval u w) := by
  rw [rotateAt,eval_append,hτ,←eval_append,List.take_append_drop]

def cycleReduce (w : Word) : List ℕ → Word
  | [] => reduce w
  | k::ks => cycleReduce (rotateAt (reduce w) k) ks

theorem trace_cycleReduce {G : Type*} [Group G] (u : Fin 4 → G)
    (hu : ∀ g, (u g)^3=1) (τ : G → ℂ) (hτ : ∀ a b, τ (a*b)=τ (b*a))
    (w : Word) (ks : List ℕ) : τ (eval u (cycleReduce w ks))=τ (eval u w) := by
  induction ks generalizing w with
  | nil => simp [cycleReduce,eval_reduce u hu]
  | cons k ks ih => rw [cycleReduce,ih,trace_rotate u τ hτ,eval_reduce u hu]

#print axioms trace_cycleReduce
#print axioms eval_inverseWord
end CGLMP3SOS


namespace CGLMP3SOS
abbrev Coeff := (ℚ × ℚ) × (ℚ × ℚ)
def coeffMul (x y : Coeff) : Coeff :=
  ((x.1.1*y.1.1+3*x.1.2*y.1.2-x.2.1*y.2.1-3*x.2.2*y.2.2,
    x.1.1*y.1.2+x.1.2*y.1.1-x.2.1*y.2.2-x.2.2*y.2.1),
   (x.1.1*y.2.1+3*x.1.2*y.2.2+x.2.1*y.1.1+3*x.2.2*y.1.2,
    x.1.1*y.2.2+x.1.2*y.2.1+x.2.1*y.1.2+x.2.2*y.1.1))
def coeffConj (x : Coeff) : Coeff := (x.1,-x.2)
noncomputable def coeffVal (s : ℝ) (x : Coeff) : ℂ :=
  ⟨(x.1.1:ℝ)+(x.1.2:ℝ)*s,(x.2.1:ℝ)+(x.2.2:ℝ)*s⟩

noncomputable def coeffValHom (s : ℝ) : Coeff →+ ℂ where
  toFun := coeffVal s
  map_zero' := by apply Complex.ext <;> simp [coeffVal]
  map_add' x y := by apply Complex.ext <;> simp [coeffVal] <;> ring

theorem coeffVal_mul (s : ℝ) (hs : s^2=3) (x y : Coeff) :
    coeffVal s (coeffMul x y)=coeffVal s x * coeffVal s y := by
  apply Complex.ext <;>
    simp [coeffVal,coeffMul,Complex.mul_re,Complex.mul_im] <;>
    ring_nf <;> rw [hs] <;> ring

theorem coeffVal_conj (s : ℝ) (x : Coeff) :
    coeffVal s (coeffConj x)=star (coeffVal s x) := by
  apply Complex.ext <;> simp [coeffVal,coeffConj]; ring

#print axioms coeffVal_mul
end CGLMP3SOS


namespace CGLMP3SOS
noncomputable section
open scoped Matrix ComplexOrder
set_option maxHeartbeats 0
set_option maxRecDepth 16384
def words : Fin 16 → Word := ![[(0,1)],[(1,1)],[(2,1)],[(3,1)],[(0,2),(1,2)],[(0,2),(2,2)],[(0,2),(3,2)],[(1,2),(0,2)],[(1,2),(2,2)],[(1,2),(3,2)],[(2,2),(0,2)],[(2,2),(1,2)],[(2,2),(3,2)],[(3,2),(0,2)],[(3,2),(1,2)],[(3,2),(2,2)]]
def labels : Fin 113 → Word := ![[],[(0,1),(1,2)],[(0,1),(2,2)],[(0,1),(3,2)],[(0,2),(1,1)],[(0,2),(2,1)],[(0,2),(3,1)],[(1,1),(2,2)],[(1,1),(3,2)],[(1,2),(2,1)],[(1,2),(3,1)],[(2,1),(3,2)],[(2,2),(3,1)],[(0,1),(1,1),(2,1)],[(0,1),(1,1),(3,1)],[(0,1),(2,1),(1,1)],[(0,1),(2,1),(3,1)],[(0,1),(3,1),(1,1)],[(0,1),(3,1),(2,1)],[(0,2),(1,2),(2,2)],[(0,2),(1,2),(3,2)],[(0,2),(2,2),(1,2)],[(0,2),(2,2),(3,2)],[(0,2),(3,2),(1,2)],[(0,2),(3,2),(2,2)],[(1,1),(2,1),(3,1)],[(1,1),(3,1),(2,1)],[(1,2),(2,2),(3,2)],[(1,2),(3,2),(2,2)],[(0,1),(1,1),(0,2),(1,2)],[(0,1),(1,1),(0,2),(2,2)],[(0,1),(1,1),(0,2),(3,2)],[(0,1),(1,1),(2,2),(1,2)],[(0,1),(1,1),(2,2),(3,2)],[(0,1),(1,1),(3,2),(1,2)],[(0,1),(1,1),(3,2),(2,2)],[(0,1),(1,2),(0,2),(1,1)],[(0,1),(1,2),(0,2),(2,1)],[(0,1),(1,2),(0,2),(3,1)],[(0,1),(1,2),(2,2),(1,1)],[(0,1),(1,2),(2,2),(3,1)],[(0,1),(1,2),(3,2),(1,1)],[(0,1),(1,2),(3,2),(2,1)],[(0,1),(2,1),(0,2),(1,2)],[(0,1),(2,1),(0,2),(2,2)],[(0,1),(2,1),(0,2),(3,2)],[(0,1),(2,1),(1,2),(2,2)],[(0,1),(2,1),(1,2),(3,2)],[(0,1),(2,1),(3,2),(1,2)],[(0,1),(2,1),(3,2),(2,2)],[(0,1),(2,2),(0,2),(1,1)],[(0,1),(2,2),(0,2),(2,1)],[(0,1),(2,2),(0,2),(3,1)],[(0,1),(2,2),(1,2),(2,1)],[(0,1),(2,2),(1,2),(3,1)],[(0,1),(2,2),(3,2),(1,1)],[(0,1),(2,2),(3,2),(2,1)],[(0,1),(3,1),(0,2),(1,2)],[(0,1),(3,1),(0,2),(2,2)],[(0,1),(3,1),(0,2),(3,2)],[(0,1),(3,1),(1,2),(2,2)],[(0,1),(3,1),(1,2),(3,2)],[(0,1),(3,1),(2,2),(1,2)],[(0,1),(3,1),(2,2),(3,2)],[(0,1),(3,2),(0,2),(1,1)],[(0,1),(3,2),(0,2),(2,1)],[(0,1),(3,2),(0,2),(3,1)],[(0,1),(3,2),(1,2),(2,1)],[(0,1),(3,2),(1,2),(3,1)],[(0,1),(3,2),(2,2),(1,1)],[(0,1),(3,2),(2,2),(3,1)],[(0,2),(1,1),(2,1),(1,2)],[(0,2),(1,1),(2,1),(3,2)],[(0,2),(1,1),(3,1),(1,2)],[(0,2),(1,1),(3,1),(2,2)],[(0,2),(1,2),(2,1),(1,1)],[(0,2),(1,2),(2,1),(3,1)],[(0,2),(1,2),(3,1),(1,1)],[(0,2),(1,2),(3,1),(2,1)],[(0,2),(2,1),(1,1),(2,2)],[(0,2),(2,1),(1,1),(3,2)],[(0,2),(2,1),(3,1),(1,2)],[(0,2),(2,1),(3,1),(2,2)],[(0,2),(2,2),(1,1),(2,1)],[(0,2),(2,2),(1,1),(3,1)],[(0,2),(2,2),(3,1),(1,1)],[(0,2),(2,2),(3,1),(2,1)],[(0,2),(3,1),(1,1),(2,2)],[(0,2),(3,1),(1,1),(3,2)],[(0,2),(3,1),(2,1),(1,2)],[(0,2),(3,1),(2,1),(3,2)],[(0,2),(3,2),(1,1),(2,1)],[(0,2),(3,2),(1,1),(3,1)],[(0,2),(3,2),(2,1),(1,1)],[(0,2),(3,2),(2,1),(3,1)],[(1,1),(2,1),(1,2),(2,2)],[(1,1),(2,1),(1,2),(3,2)],[(1,1),(2,1),(3,2),(2,2)],[(1,1),(2,2),(1,2),(2,1)],[(1,1),(2,2),(1,2),(3,1)],[(1,1),(2,2),(3,2),(2,1)],[(1,1),(3,1),(1,2),(2,2)],[(1,1),(3,1),(1,2),(3,2)],[(1,1),(3,1),(2,2),(3,2)],[(1,1),(3,2),(1,2),(2,1)],[(1,1),(3,2),(1,2),(3,1)],[(1,1),(3,2),(2,2),(3,1)],[(1,2),(2,1),(3,1),(2,2)],[(1,2),(2,2),(3,1),(2,1)],[(1,2),(3,1),(2,1),(3,2)],[(1,2),(3,2),(2,1),(3,1)],[(2,1),(3,1),(2,2),(3,2)],[(2,1),(3,2),(2,2),(3,1)]]
def momentIndex : Fin 16 → Fin 16 → Fin 113 := ![![0,1,2,3,4,5,6,4,15,17,5,13,18,6,14,16],![4,0,7,8,1,13,14,1,9,10,15,9,26,17,10,25],![5,9,0,11,15,2,16,13,7,25,2,7,12,18,26,12],![6,10,12,0,17,18,3,14,26,8,16,25,11,3,8,11],![1,4,19,20,0,9,10,29,75,77,43,5,78,57,6,76],![2,21,5,22,7,0,12,30,4,85,44,83,86,58,84,6],![3,23,24,6,8,11,0,31,93,4,45,91,5,59,92,94],![1,4,21,23,36,37,38,0,5,6,9,71,89,10,73,81],![19,7,9,27,39,1,40,2,0,12,46,95,108,60,101,10],![20,8,28,10,41,42,1,3,11,0,47,96,9,61,102,110],![2,19,5,24,50,51,52,7,79,87,0,4,6,12,74,82],![21,7,9,28,2,53,54,32,98,99,1,0,10,62,12,107],![22,27,11,12,55,56,2,33,100,7,3,8,0,63,103,111],![3,20,22,6,64,65,66,8,80,88,11,72,90,0,4,5],![23,8,27,10,3,67,68,34,104,105,48,11,109,1,0,9],![24,28,11,12,69,3,70,35,8,106,49,97,112,2,7,0]]
def rotations : Fin 16 → Fin 16 → List ℕ := ![![[],[1],[1],[1],[1],[1],[1],[2],[2],[2],[2],[2],[2],[2],[2],[2]],![[],[],[1],[1],[1],[1],[1],[],[1],[1],[],[2],[2],[],[2],[2]],![[],[],[],[1],[1],[1],[1],[],[1],[1],[],[],[1],[],[],[2]],![[],[],[],[],[1],[1],[1],[],[1],[1],[],[],[1],[],[],[]],![[],[1],[1],[1],[],[1],[1],[],[2],[2],[],[2],[2],[],[2],[2]],![[],[1],[1],[1],[],[],[1],[],[2],[2],[],[2],[2],[],[2],[2]],![[],[1],[1],[1],[],[],[],[],[2],[2],[],[2],[2],[],[2],[2]],![[2],[1],[2],[2],[1],[1],[1],[],[1],[1],[2],[3],[3],[2],[3],[3]],![[],[],[1],[1],[1],[1],[1],[],[],[1],[],[],[2],[],[],[2]],![[],[],[1],[1],[1],[1],[1],[],[],[],[],[],[2],[],[],[2]],![[2],[2],[1],[2],[1],[1],[1],[1],[3],[3],[],[1],[1],[2],[3],[3]],![[],[2],[1],[2],[1],[1],[1],[],[1],[1],[],[],[1],[],[2],[3]],![[],[],[],[1],[1],[1],[1],[],[1],[1],[],[],[],[],[],[]],![[2],[2],[2],[1],[1],[1],[1],[1],[3],[3],[1],[3],[3],[],[1],[1]],![[],[2],[2],[1],[1],[1],[1],[],[1],[1],[],[1],[3],[],[],[1]],![[],[],[2],[1],[1],[1],[1],[],[1],[1],[],[],[1],[],[],[]]]
def objectiveWords : Fin 8 → Word := ![[(0,1),(2,2)],[(2,1),(1,2)],[(1,1),(3,2)],[(3,1),(0,2)],[(2,1),(0,2)],[(1,1),(2,2)],[(3,1),(1,2)],[(0,1),(3,2)]]
def objectiveIndex : Fin 8 → Fin 113 := ![2,9,8,6,5,7,10,3]
def objectiveRotations : Fin 8 → List ℕ := ![[],[1],[],[1],[1],[],[1],[]]
def Draw : Fin 13 → Coeff := ![(((1123:ℚ)/3300,(-19:ℚ)/4950),((0:ℚ),(0:ℚ))),(((11253553:ℚ)/453833160,(224570891:ℚ)/1701874350),((0:ℚ),(0:ℚ))),(((689564837350273:ℚ)/1391596903930200,(-310423590209047:ℚ)/2087395355895300),((0:ℚ),(0:ℚ))),(((-1085431639818886117079:ℚ)/5924918589013225599600,(1463662777494345179699:ℚ)/8887377883519838399400),((0:ℚ),(0:ℚ))),(((9563584948710758348239613:ℚ)/101971008615703842091095700,(-386628812616409233030149:ℚ)/40788403446281536836438280),((0:ℚ),(0:ℚ))),(((4846568693919992943808056117:ℚ)/34778266410549606636377509300,(-674795205064087197871063929:ℚ)/34778266410549606636377509300),((0:ℚ),(0:ℚ))),(((3535367524302920921160345053:ℚ)/42408060515713477158975357108,(9901012972176733330162252141:ℚ)/1060201512892836928974383927700),((0:ℚ),(0:ℚ))),(((-37978513643482111251272113472433:ℚ)/212723933395360710288225332649800,(15467917190965470196738828521001:ℚ)/106361966697680355144112666324900),((0:ℚ),(0:ℚ))),(((304398136052758282075887501636749:ℚ)/44775091839972633469346872391440900,(324846374546548806582091078616887:ℚ)/5373011020796716016321624686972908),((0:ℚ),(0:ℚ))),(((-808245780583934104382858914608915467:ℚ)/3666952541887063179627701246006078950,(58419052794150592653236567118568147:ℚ)/366695254188706317962770124600607895),((0:ℚ),(0:ℚ))),(((-1809910766201715706680700912068641339:ℚ)/252644718431023571471714217839802380450,(4870248491623362021588123803836214469:ℚ)/126322359215511785735857108919901190225),((0:ℚ),(0:ℚ))),(((16501961346840265443261492024902921799:ℚ)/556821589636986302571592175724189055790,(24146004133989870651740893474028962317:ℚ)/2784107948184931512857960878620945278950),((0:ℚ),(0:ℚ))),(((5841610670388940529444082996321258113:ℚ)/75709164218071216070233342202512328835,(-441286724872458925191949773625377184:ℚ)/25236388072690405356744447400837442945),((0:ℚ),(0:ℚ)))]
def Vraw : Matrix (Fin 16) (Fin 13) Coeff := ![![(((-121169:ℚ)/687626,(257397:ℚ)/1375252),((724559:ℚ)/1375252,(-245941:ℚ)/687626)),(((-555867350131:ℚ)/843392062988,(112832762615:ℚ)/843392062988),((-832824460523:ℚ)/843392062988,(577927101037:ℚ)/843392062988)),(((166670959701386911:ℚ)/1795429875458553212,(310270084464493711:ℚ)/1795429875458553212),((-1105704058712689641:ℚ)/1795429875458553212,(478243077137258861:ℚ)/1795429875458553212)),(((-999071500515040243083521:ℚ)/2039420172314076841821914,(148399999716240267688324:ℚ)/1019710086157038420910957),((-70622431166962243008524:ℚ)/1019710086157038420910957,(-327783887296794651062203:ℚ)/2039420172314076841821914)),(((-115375476923509655732734286:ℚ)/347782664105496066363775093,(-63023475270639944448813519:ℚ)/347782664105496066363775093),((-97124058238819934966150799:ℚ)/347782664105496066363775093,(-2446013754184320323062588:ℚ)/347782664105496066363775093)),(((601197454841534387480783231:ℚ)/7068010085952246193162559518,(2759677761195178563590447711:ℚ)/21204030257856738579487678554),((2696295666904777717854408275:ℚ)/7068010085952246193162559518,(-1529925782025799826309652607:ℚ)/21204030257856738579487678554)),(((-849439732997306880038489012319:ℚ)/2127239333953607102882253326498,(256487087094106055612134705783:ℚ)/1063619666976803551441126663249),((-454154721012973131857895574059:ℚ)/1063619666976803551441126663249,(481549309162626197004715716403:ℚ)/2127239333953607102882253326498)),(((373223723078665807152495478782123:ℚ)/895501836799452669386937447828818,(-256134957155113822525625306523419:ℚ)/2686505510398358008160812343486454),((51906238552678067293319444377575:ℚ)/895501836799452669386937447828818,(-187092635917162899176016100862321:ℚ)/2686505510398358008160812343486454)),(((2312503070131449328526248326559123:ℚ)/146678101675482527185108049840243158,(-29041801529518449688567894373239529:ℚ)/73339050837741263592554024920121579),((16439876873321095611104758282021281:ℚ)/73339050837741263592554024920121579,(-38736821268525707194758796795534401:ℚ)/146678101675482527185108049840243158)),(((-1705793681095503037652612426933026333:ℚ)/5052894368620471429434284356796047609,(680887863283845233482160654059017655:ℚ)/10105788737240942858868568713592095218),((-917276212683019843396379241014475101:ℚ)/10105788737240942858868568713592095218,(387868349599238526319431033867662832:ℚ)/5052894368620471429434284356796047609)),(((62535777344195741106934621511184205679:ℚ)/111364317927397260514318435144837811158,(-4816064943616512960629434109699243362:ℚ)/55682158963698630257159217572418905579),((27437626034044400218941825837672484570:ℚ)/55682158963698630257159217572418905579,(1626076995709288934844021745546638915:ℚ)/111364317927397260514318435144837811158)),(((987185618917553956093058904566188918:ℚ)/5047277614538081071348889480167488589,(-919312249702728127628116883249247715:ℚ)/30283665687228486428093336881004931534),((5788004657469965508420765808425291617:ℚ)/30283665687228486428093336881004931534,(-6367023375241313093459371534216175632:ℚ)/15141832843614243214046668440502465767)),(((3:ℚ)/10,(1:ℚ)/10),((-1:ℚ)/10,(3:ℚ)/10))],![(((1:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ)))],![(((-314739:ℚ)/687626,(-9367:ℚ)/687626),((-74059:ℚ)/343813,(82337:ℚ)/343813)),(((1:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ)))],![(((-170451:ℚ)/343813,(38490:ℚ)/343813),((187017:ℚ)/343813,(-146070:ℚ)/343813)),(((181409748754:ℚ)/210848015747,(-210630347749:ℚ)/421696031494),((-474856293713:ℚ)/421696031494,(119563464154:ℚ)/210848015747)),(((1:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ)))],![(((128710:ℚ)/343813,(-292899:ℚ)/1375252),((446973:ℚ)/1375252,(-70227:ℚ)/343813)),(((168838942697:ℚ)/843392062988,(-64023505305:ℚ)/843392062988),((-368793502165:ℚ)/843392062988,(200339614047:ℚ)/843392062988)),(((277954586146991283:ℚ)/897714937729276606,(-154557449264156035:ℚ)/897714937729276606),((39929039758214218:ℚ)/448857468864638303,(-39032818630647567:ℚ)/448857468864638303)),(((1:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ)))],![(((-69723:ℚ)/343813,(29523:ℚ)/343813),((50193:ℚ)/343813,(-9537:ℚ)/343813)),(((133990557283:ℚ)/210848015747,(-90213538623:ℚ)/210848015747),((-43763522202:ℚ)/210848015747,(2266722840:ℚ)/210848015747)),(((100160791686646801:ℚ)/897714937729276606,(-52908355767463741:ℚ)/897714937729276606),((271655049619174331:ℚ)/897714937729276606,(-119922124993386929:ℚ)/897714937729276606)),(((20003667340343097292188:ℚ)/1019710086157038420910957,(-69353296762160138621954:ℚ)/1019710086157038420910957),((146117237778049276060748:ℚ)/1019710086157038420910957,(-61357045093568726079180:ℚ)/1019710086157038420910957)),(((1:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ)))],![(((19872:ℚ)/343813,(-9879:ℚ)/343813),((49851:ℚ)/343813,(-19644:ℚ)/343813)),(((-52888255119:ℚ)/210848015747,(21360832089:ℚ)/210848015747),((33857973675:ℚ)/210848015747,(-23119067055:ℚ)/210848015747)),(((55845986138626833:ℚ)/448857468864638303,(72306634086124965:ℚ)/448857468864638303),((45049653713727315:ℚ)/448857468864638303,(3216179302764651:ℚ)/448857468864638303)),(((-159946985912707528389648:ℚ)/1019710086157038420910957,(-283868935502045343810378:ℚ)/1019710086157038420910957),((142641665092646955581076:ℚ)/1019710086157038420910957,(-113406620440778044757970:ℚ)/1019710086157038420910957)),(((-249568448032036978689158257:ℚ)/347782664105496066363775093,(56381843859965112723247861:ℚ)/347782664105496066363775093),((53001498188130706053947537:ℚ)/347782664105496066363775093,(-11339361138812751972413343:ℚ)/347782664105496066363775093)),(((1:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ)))],![(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((-2025639540:ℚ)/210848015747,(10779402768:ℚ)/210848015747),((0:ℚ),(0:ℚ))),(((-35019021428507160:ℚ)/448857468864638303,(-1460798467564986:ℚ)/448857468864638303),((-40104025612657146:ℚ)/448857468864638303,(-1762636998264588:ℚ)/448857468864638303)),(((-57828390350837454368496:ℚ)/1019710086157038420910957,(18633485255431470887568:ℚ)/1019710086157038420910957),((-3581839804029233584392:ℚ)/1019710086157038420910957,(7674405363466222856496:ℚ)/1019710086157038420910957)),(((23494770437736868372579562:ℚ)/347782664105496066363775093,(-4114745771389914989646594:ℚ)/347782664105496066363775093),((-28826004410011173502214846:ℚ)/347782664105496066363775093,(3708084702110829889864666:ℚ)/347782664105496066363775093)),(((226366303482635093671625833:ℚ)/3534005042976123096581279759,(337431853586048112257119543:ℚ)/10602015128928369289743839277),((105231884612277982642089109:ℚ)/10602015128928369289743839277,(82516291708901413750673257:ℚ)/3534005042976123096581279759)),(((1:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ)))],![(((40840:ℚ)/343813,(-59750:ℚ)/343813),((19789:ℚ)/343813,(-39475:ℚ)/343813)),(((-42544656132:ℚ)/210848015747,(-9106900347:ℚ)/210848015747),((187253375168:ℚ)/210848015747,(-100688825589:ℚ)/210848015747)),(((-228610073952857318:ℚ)/448857468864638303,(106558399575655864:ℚ)/448857468864638303),((146825549775756369:ℚ)/448857468864638303,(-70644641857262329:ℚ)/448857468864638303)),(((201134879937142495402097:ℚ)/1019710086157038420910957,(-85804184737825077079508:ℚ)/1019710086157038420910957),((361875730605747010296898:ℚ)/1019710086157038420910957,(-185572936442630092260071:ℚ)/1019710086157038420910957)),(((2861973903323173418284457:ℚ)/347782664105496066363775093,(-2402398245496073637697483:ℚ)/695565328210992132727550186),((132846756408927037786081011:ℚ)/695565328210992132727550186,(-14333796816829252897286691:ℚ)/347782664105496066363775093)),(((3537057329793246575599913950:ℚ)/10602015128928369289743839277,(-515772155128233131074327505:ℚ)/3534005042976123096581279759),((-869241956678000352861521081:ℚ)/10602015128928369289743839277,(461512289786203493964777817:ℚ)/10602015128928369289743839277)),(((-113821624305726039133124991920:ℚ)/1063619666976803551441126663249,(-120087940463848945396736357605:ℚ)/1063619666976803551441126663249),((-409301238593003770324909220977:ℚ)/1063619666976803551441126663249,(217617424938151664009694222682:ℚ)/1063619666976803551441126663249)),(((27966643373580507935211957359609:ℚ)/447750918399726334693468723914409,(-18082673050473346216638720870443:ℚ)/2686505510398358008160812343486454),((-129182304956920225652650439827113:ℚ)/895501836799452669386937447828818,(197165559119210897870951835777629:ℚ)/1343252755199179004080406171743227)),(((-8560477003978544291724732779076881:ℚ)/146678101675482527185108049840243158,(-7369659916797561009471587735932255:ℚ)/73339050837741263592554024920121579),((12442531408729385229526331791198239:ℚ)/73339050837741263592554024920121579,(-5225763530252357587315553201359865:ℚ)/146678101675482527185108049840243158)),(((-4419535470786113800169267952553408603:ℚ)/10105788737240942858868568713592095218,(-700592520965731980339498275474788547:ℚ)/5052894368620471429434284356796047609),((-211276991946613202854447834194617393:ℚ)/5052894368620471429434284356796047609,(548522225384489104026931676772480325:ℚ)/10105788737240942858868568713592095218)),(((-6148770275385243512935803790019845508:ℚ)/55682158963698630257159217572418905579,(3911764160107570498489397699526542105:ℚ)/111364317927397260514318435144837811158),((2445377107327121743874248099548120047:ℚ)/111364317927397260514318435144837811158,(-5427654048447432674568077575667620148:ℚ)/55682158963698630257159217572418905579)),(((-11711118370975289244979119235822425125:ℚ)/30283665687228486428093336881004931534,(-248078973904814816583301414803477798:ℚ)/5047277614538081071348889480167488589),((-7503361893789442492954540410765311938:ℚ)/15141832843614243214046668440502465767,(11814734500779898059290626185183103549:ℚ)/30283665687228486428093336881004931534)),(((-1:ℚ)/5,(-2:ℚ)/5),((2:ℚ)/5,(-1:ℚ)/5))],![(((-60642:ℚ)/343813,(-684:ℚ)/343813),((60642:ℚ)/343813,(684:ℚ)/343813)),(((-23082286122:ℚ)/210848015747,(-6297888114:ℚ)/210848015747),((-23976569034:ℚ)/210848015747,(12360725850:ℚ)/210848015747)),(((-95005899981150120:ℚ)/448857468864638303,(-18375166251328116:ℚ)/448857468864638303),((-81496134695060964:ℚ)/448857468864638303,(20356036276331424:ℚ)/448857468864638303)),(((-141509394062127965629386:ℚ)/1019710086157038420910957,(104993401961687648916834:ℚ)/1019710086157038420910957),((53041367335146507679734:ℚ)/1019710086157038420910957,(10286089285339847430774:ℚ)/1019710086157038420910957)),(((87472222270840412452254346:ℚ)/347782664105496066363775093,(-80379628744868787297187854:ℚ)/347782664105496066363775093),((-43931233456958532142710538:ℚ)/347782664105496066363775093,(28103596425858952434026674:ℚ)/347782664105496066363775093)),(((27851897789628637408305304:ℚ)/10602015128928369289743839277,(115010910209904154658690950:ℚ)/10602015128928369289743839277),((261880751442822378578208047:ℚ)/10602015128928369289743839277,(63179269718955172679242987:ℚ)/10602015128928369289743839277)),(((90132257190665252447464524737:ℚ)/1063619666976803551441126663249,(43151768347569361806302220557:ℚ)/1063619666976803551441126663249),((-578663131880154901012815592162:ℚ)/1063619666976803551441126663249,(119641315999523625968723042980:ℚ)/1063619666976803551441126663249)),(((1:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ)))],![(((-20214:ℚ)/343813,(-228:ℚ)/343813),((89937:ℚ)/687626,(-29295:ℚ)/687626)),(((-18158953338:ℚ)/210848015747,(-24793142400:ℚ)/210848015747),((-14238057690:ℚ)/210848015747,(-18126921639:ℚ)/210848015747)),(((-14482100352358809:ℚ)/448857468864638303,(37142136914003361:ℚ)/897714937729276606),((98576395993577403:ℚ)/897714937729276606,(-6801459046465413:ℚ)/448857468864638303)),(((89730357640857873106209:ℚ)/2039420172314076841821914,(10532390515889549568177:ℚ)/2039420172314076841821914),((317824389461596339996515:ℚ)/2039420172314076841821914,(-121988047672491793680207:ℚ)/2039420172314076841821914)),(((-45625689291839270338267545:ℚ)/347782664105496066363775093,(-31375594083456201318545879:ℚ)/347782664105496066363775093),((16062969618778744885380407:ℚ)/347782664105496066363775093,(12434086339006916630793723:ℚ)/347782664105496066363775093)),(((-1569054380062054793766198745:ℚ)/21204030257856738579487678554,(-1486245691705323597854396597:ℚ)/21204030257856738579487678554),((313327100232153107771906801:ℚ)/21204030257856738579487678554,(-267686712761760392592778775:ℚ)/7068010085952246193162559518)),(((-485854474636118118535784733107:ℚ)/1063619666976803551441126663249,(113295367954590497382472601371:ℚ)/1063619666976803551441126663249),((41732729665791491371151096015:ℚ)/1063619666976803551441126663249,(12392578924580730187805917187:ℚ)/1063619666976803551441126663249)),(((-32871894950814834035774979960822:ℚ)/447750918399726334693468723914409,(-69223788509576242550080556907478:ℚ)/1343252755199179004080406171743227),((-4432678269212217797343029735694:ℚ)/447750918399726334693468723914409,(66633359969716760612439886861358:ℚ)/1343252755199179004080406171743227)),(((1:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ)))],![(((-80172:ℚ)/343813,(19302:ℚ)/343813),((-60642:ℚ)/343813,(-684:ℚ)/343813)),(((47284789302:ℚ)/210848015747,(-60871326786:ℚ)/210848015747),((-45761074110:ℚ)/210848015747,(37028109390:ℚ)/210848015747)),(((96014773596594294:ℚ)/448857468864638303,(-101572211369419410:ℚ)/448857468864638303),((7589116907483274:ℚ)/448857468864638303,(18219273362454630:ℚ)/448857468864638303)),(((-125123815796337800539740:ℚ)/1019710086157038420910957,(-125883895223548834676316:ℚ)/1019710086157038420910957),((-185933969355803228292852:ℚ)/1019710086157038420910957,(132139828827690772996068:ℚ)/1019710086157038420910957)),(((118248189216455918599584380:ℚ)/347782664105496066363775093,(-79684298604618972880245396:ℚ)/347782664105496066363775093),((101966534228474211566264284:ℚ)/347782664105496066363775093,(-49238985213754755634728068:ℚ)/347782664105496066363775093)),(((26021014463121071738375092:ℚ)/3534005042976123096581279759,(-666642096481584582010975682:ℚ)/10602015128928369289743839277),((-82118229662441233416306278:ℚ)/10602015128928369289743839277,(-86170070567021441794631036:ℚ)/3534005042976123096581279759)),(((133620201095199994362935704600:ℚ)/1063619666976803551441126663249,(-45945678556609787056078254252:ℚ)/1063619666976803551441126663249),((-189933873930908759062952393940:ℚ)/1063619666976803551441126663249,(134609667881760022490583316320:ℚ)/1063619666976803551441126663249)),(((-41741653597907710540209064264616:ℚ)/447750918399726334693468723914409,(-105274193382337759580884055922992:ℚ)/1343252755199179004080406171743227),((38586685344323050725778515813632:ℚ)/447750918399726334693468723914409,(-162297597939382839889703020894408:ℚ)/1343252755199179004080406171743227)),(((-12146916510028853455783515413878935:ℚ)/73339050837741263592554024920121579,(7703924799104862677731458009637011:ℚ)/73339050837741263592554024920121579),((12202813506584963923409395830952292:ℚ)/73339050837741263592554024920121579,(-4114422554268370450204255827956904:ℚ)/73339050837741263592554024920121579)),(((1:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ)))],![(((-125013:ℚ)/1375252,(114623:ℚ)/1375252),((752779:ℚ)/1375252,(-399819:ℚ)/1375252)),(((-52789851575:ℚ)/210848015747,(25423387792:ℚ)/210848015747),((-78911562127:ℚ)/210848015747,(53086802155:ℚ)/210848015747)),(((123746658742811059:ℚ)/897714937729276606,(-88022741817593151:ℚ)/897714937729276606),((-323946569403275679:ℚ)/897714937729276606,(160937972577508335:ℚ)/897714937729276606)),(((220101620058298244611833:ℚ)/2039420172314076841821914,(-117855844142744478514997:ℚ)/2039420172314076841821914),((204869857669470311614961:ℚ)/2039420172314076841821914,(-127415337118898361591015:ℚ)/2039420172314076841821914)),(((111414061365198019295728258:ℚ)/347782664105496066363775093,(-58054936886349858058625055:ℚ)/347782664105496066363775093),((146865770650715307653726404:ℚ)/347782664105496066363775093,(-69988451185341746993173071:ℚ)/347782664105496066363775093)),(((150186565592820767393108235:ℚ)/3534005042976123096581279759,(-3466393894936200345883379416:ℚ)/10602015128928369289743839277),((-645201476632462426770156683:ℚ)/3534005042976123096581279759,(1481312582290721435478683336:ℚ)/10602015128928369289743839277)),(((-359450779466588682569278550931:ℚ)/2127239333953607102882253326498,(276728600089228918454677653553:ℚ)/2127239333953607102882253326498),((-1061986094567256526022470647897:ℚ)/2127239333953607102882253326498,(545494838258485484650901249237:ℚ)/2127239333953607102882253326498)),(((59727163487740444929088574671341:ℚ)/447750918399726334693468723914409,(-486000944474724746582590523068924:ℚ)/1343252755199179004080406171743227),((191897509276174104273363961987692:ℚ)/447750918399726334693468723914409,(-343605671332772695853573431295857:ℚ)/1343252755199179004080406171743227)),(((11807751668612155015117203195804278:ℚ)/73339050837741263592554024920121579,(-2580342671302512188921951409074114:ℚ)/73339050837741263592554024920121579),((-9297794554801991791990807565662968:ℚ)/73339050837741263592554024920121579,(-12785432219894902063577812104353649:ℚ)/73339050837741263592554024920121579)),(((-379660589982701434123984848953509359:ℚ)/5052894368620471429434284356796047609,(-1639540386518208082737370210318899063:ℚ)/5052894368620471429434284356796047609),((-1941521259485881797471849134127522338:ℚ)/5052894368620471429434284356796047609,(1401938641597993876055299669652692073:ℚ)/5052894368620471429434284356796047609)),(((24258067461665203322063231262071908391:ℚ)/111364317927397260514318435144837811158,(-1966801111580090934091679520477992869:ℚ)/111364317927397260514318435144837811158),((12982795716730940902969924405182553131:ℚ)/111364317927397260514318435144837811158,(-27766932835725324313585894147988565153:ℚ)/111364317927397260514318435144837811158)),(((-1317662782161527285926206919383502939:ℚ)/15141832843614243214046668440502465767,(-563151067956108260318632621666616905:ℚ)/10094555229076162142697778960334977178),((1637645138966020373800144390319511503:ℚ)/30283665687228486428093336881004931534,(2061899703875971735676111163793936333:ℚ)/15141832843614243214046668440502465767)),(((2:ℚ)/5,(0:ℚ)),((1:ℚ)/5,(0:ℚ)))],![(((-10107:ℚ)/343813,(-114:ℚ)/343813),((49851:ℚ)/343813,(-19644:ℚ)/343813)),(((-28629666171:ℚ)/210848015747,(12745181265:ℚ)/210848015747),((-18000377739:ℚ)/210848015747,(3376611321:ℚ)/210848015747)),(((52159916116142892:ℚ)/448857468864638303,(54609233792318421:ℚ)/448857468864638303),((2957130653101749:ℚ)/448857468864638303,(28373584253968134:ℚ)/448857468864638303)),(((-9086114068025076062703:ℚ)/1019710086157038420910957,(13755153876828041663793:ℚ)/1019710086157038420910957),((78240550945437056431251:ℚ)/1019710086157038420910957,(-66527036816717365422339:ℚ)/1019710086157038420910957)),(((-27037447482889935474947498:ℚ)/347782664105496066363775093,(-5285630515148880453154902:ℚ)/347782664105496066363775093),((-21614479912210535408707326:ℚ)/347782664105496066363775093,(24858811366011932259479418:ℚ)/347782664105496066363775093)),(((-1596548659701003996721414276:ℚ)/10602015128928369289743839277,(-1357306180826128479669444962:ℚ)/10602015128928369289743839277),((43118047916089397211937426:ℚ)/10602015128928369289743839277,(-103897258870702656600334224:ℚ)/3534005042976123096581279759)),(((-513044840955893272358674481978:ℚ)/1063619666976803551441126663249,(144972754251683775798895859126:ℚ)/1063619666976803551441126663249),((-56687811932251642408375218332:ℚ)/1063619666976803551441126663249,(689172413127088402189357248:ℚ)/1063619666976803551441126663249)),(((81345500285181895805567958779344:ℚ)/447750918399726334693468723914409,(78565624679337261552486252406648:ℚ)/1343252755199179004080406171743227),((4729844781425410297145711819024:ℚ)/447750918399726334693468723914409,(70452483373704706916340148300120:ℚ)/1343252755199179004080406171743227)),(((2836168513330418122853256566107174:ℚ)/73339050837741263592554024920121579,(-19295606204883257642340436437406684:ℚ)/73339050837741263592554024920121579),((3857238940517570144065135859750073:ℚ)/73339050837741263592554024920121579,(-343700110207903362633569559501789:ℚ)/73339050837741263592554024920121579)),(((758075204702023991157177798631469282:ℚ)/5052894368620471429434284356796047609,(361184862522468236181692421542879896:ℚ)/5052894368620471429434284356796047609),((51333532009222609279617710176394161:ℚ)/5052894368620471429434284356796047609,(293841971170472147152239341487456319:ℚ)/5052894368620471429434284356796047609)),(((1:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ)))],![(((-684:ℚ)/343813,(-20214:ℚ)/343813),((-18846:ℚ)/343813,(40200:ℚ)/343813)),(((12329620794:ℚ)/210848015747,(-29461287342:ℚ)/210848015747),((40371430266:ℚ)/210848015747,(-24839795490:ℚ)/210848015747)),(((-54033179830705548:ℚ)/448857468864638303,(-35979194247210060:ℚ)/448857468864638303),((26895430727191476:ℚ)/448857468864638303,(-50162120683918956:ℚ)/448857468864638303)),(((36214505627725560001212:ℚ)/1019710086157038420910957,(29988138048509593741944:ℚ)/1019710086157038420910957),((-185556653914243555629144:ℚ)/1019710086157038420910957,(-87195685025412177036972:ℚ)/1019710086157038420910957)),(((-38652195461521565589927932:ℚ)/347782664105496066363775093,(3685064611683090118890788:ℚ)/347782664105496066363775093),((106216775370564412503741124:ℚ)/347782664105496066363775093,(-59594908657891406397525396:ℚ)/347782664105496066363775093)),(((255286846203878128717833760:ℚ)/10602015128928369289743839277,(1215325902827653168248312146:ℚ)/10602015128928369289743839277),((256070624459122019612654238:ℚ)/3534005042976123096581279759,(-483216855936682882057867608:ℚ)/3534005042976123096581279759)),(((140814136688598032153614558776:ℚ)/1063619666976803551441126663249,(-115562976221626504532942293556:ℚ)/1063619666976803551441126663249),((50986002255027767774154502172:ℚ)/1063619666976803551441126663249,(10353918974755562009941410616:ℚ)/1063619666976803551441126663249)),(((-161687648258374099271905774575200:ℚ)/447750918399726334693468723914409,(-134374113013187216617315405492792:ℚ)/1343252755199179004080406171743227),((26858360820350000659945799655032:ℚ)/447750918399726334693468723914409,(-2782416704771145415216949918944:ℚ)/1343252755199179004080406171743227)),(((-11534879460510590811112646310788944:ℚ)/73339050837741263592554024920121579,(-811295784553613380414388591056787:ℚ)/73339050837741263592554024920121579),((-5768277587584287039505677621617775:ℚ)/73339050837741263592554024920121579,(4243489224049184830747406489542056:ℚ)/73339050837741263592554024920121579)),(((344570781368693838297407528406807:ℚ)/219691059505237888236273232904175983,(1120365205055089276494614387292435:ℚ)/219691059505237888236273232904175983),((-81455518674443682238530538381601701:ℚ)/5052894368620471429434284356796047609,(-659005076522598188640518299087637006:ℚ)/5052894368620471429434284356796047609)),(((4374503590757079597238267014816758401:ℚ)/55682158963698630257159217572418905579,(1461982569958939122101258681184610503:ℚ)/55682158963698630257159217572418905579),((-1864881356006388629067993494794495846:ℚ)/55682158963698630257159217572418905579,(280214859340913109312818240491452697:ℚ)/55682158963698630257159217572418905579)),(((1:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ)))],![(((20214:ℚ)/343813,(228:ℚ)/343813),((0:ℚ),(0:ℚ))),(((-486653742:ℚ)/210848015747,(4906336122:ℚ)/210848015747),((8180749116:ℚ)/210848015747,(-2807040084:ℚ)/210848015747)),(((-1994102244309249:ℚ)/448857468864638303,(8401349898644037:ℚ)/448857468864638303),((3745170937400355:ℚ)/448857468864638303,(-7830617590967613:ℚ)/448857468864638303)),(((14843706318594503547408:ℚ)/1019710086157038420910957,(-14712147542549765867838:ℚ)/1019710086157038420910957),((7903816487042038327998:ℚ)/1019710086157038420910957,(-12924021772678796813664:ℚ)/1019710086157038420910957)),(((65578358166077950169902916:ℚ)/347782664105496066363775093,(22116470158554506226882764:ℚ)/347782664105496066363775093),((-157989595160372437436558984:ℚ)/347782664105496066363775093,(-10256526903012583722103052:ℚ)/347782664105496066363775093)),(((477851992758510426236379106:ℚ)/3534005042976123096581279759,(-152066961635625967369566538:ℚ)/10602015128928369289743839277),((-1812151227755737863599129906:ℚ)/10602015128928369289743839277,(354982368804101619857128466:ℚ)/10602015128928369289743839277)),(((-85464453917943385528808058956:ℚ)/1063619666976803551441126663249,(17804912193490542563380220492:ℚ)/1063619666976803551441126663249),((42768609483965088743144612988:ℚ)/1063619666976803551441126663249,(-18980504544247186686597073948:ℚ)/1063619666976803551441126663249)),(((43368447567604431913031128827128:ℚ)/447750918399726334693468723914409,(51131034396013164256815921313432:ℚ)/1343252755199179004080406171743227),((-24037939282543336413542752201384:ℚ)/447750918399726334693468723914409,(28450796960126312220162022069352:ℚ)/1343252755199179004080406171743227)),(((6512144529928884120940963973081964:ℚ)/73339050837741263592554024920121579,(3185066495977165576521514898674222:ℚ)/73339050837741263592554024920121579),((-6989289224582589464696713942433194:ℚ)/73339050837741263592554024920121579,(230970770117968100842046680011424:ℚ)/73339050837741263592554024920121579)),(((539781191292829285306319978006453644:ℚ)/5052894368620471429434284356796047609,(389433896410612634768093026908616870:ℚ)/5052894368620471429434284356796047609),((-458749057136914135389640390848176906:ℚ)/5052894368620471429434284356796047609,(-51820107864940557404006615632617696:ℚ)/5052894368620471429434284356796047609)),(((1141456331814188510318678531782532012:ℚ)/55682158963698630257159217572418905579,(-17513699492425416966469252682461828620:ℚ)/55682158963698630257159217572418905579),((-406771191036875126679582500233068896:ℚ)/55682158963698630257159217572418905579,(-1269812023134960071235988229194221478:ℚ)/55682158963698630257159217572418905579)),(((-9387419416647165991975675863858483010:ℚ)/15141832843614243214046668440502465767,(372446500007646954720213298794085618:ℚ)/15141832843614243214046668440502465767),((985102640375849219908783769901004814:ℚ)/5047277614538081071348889480167488589,(-2602390412121015745193162960163434860:ℚ)/15141832843614243214046668440502465767)),(((1:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ)))]]
def Qraw : Matrix (Fin 16) (Fin 16) Coeff := ![![(((49:ℚ)/825,(469:ℚ)/3300),((0:ℚ),(0:ℚ))),(((-41:ℚ)/660,(2549:ℚ)/39600),((807:ℚ)/4400,(-49:ℚ)/396)),(((-871:ℚ)/13200,(-1651:ℚ)/39600),((1429:ℚ)/13200,(-241:ℚ)/7920)),(((-7:ℚ)/200,(13:ℚ)/200),((1:ℚ)/8,(-11:ℚ)/120)),(((-191:ℚ)/2640,(167:ℚ)/6600),((437:ℚ)/6600,(-2159:ℚ)/39600)),(((-349:ℚ)/3300,(293:ℚ)/9900),((112:ℚ)/825,(-217:ℚ)/1980)),(((27:ℚ)/200,(-3:ℚ)/200),((-3:ℚ)/200,(1:ℚ)/40)),(((-3:ℚ)/200,(1:ℚ)/200),((-3:ℚ)/200,(3:ℚ)/200)),(((53:ℚ)/300,(-89:ℚ)/900),((353:ℚ)/2200,(-1643:ℚ)/19800)),(((-17:ℚ)/400,(11:ℚ)/400),((-13:ℚ)/400,(9:ℚ)/400)),(((-9:ℚ)/400,(-9:ℚ)/400),((-11:ℚ)/400,(-9:ℚ)/400)),(((1:ℚ)/20,(-3:ℚ)/100),((1:ℚ)/20,(-1:ℚ)/100)),(((797:ℚ)/6600,(-1477:ℚ)/19800),((-1:ℚ)/50,(0:ℚ))),(((9:ℚ)/200,(3:ℚ)/200),((-7:ℚ)/200,(1:ℚ)/40)),(((0:ℚ),(1:ℚ)/100),((3:ℚ)/100,(-1:ℚ)/50)),(((-1:ℚ)/50,(1:ℚ)/100),((-1:ℚ)/20,(1:ℚ)/50))],![(((-41:ℚ)/660,(2549:ℚ)/39600),((-807:ℚ)/4400,(49:ℚ)/396)),(((1123:ℚ)/3300,(-19:ℚ)/4950),((0:ℚ),(0:ℚ))),(((-1027:ℚ)/6600,(-19:ℚ)/6600),((251:ℚ)/3300,(-163:ℚ)/1980)),(((-17:ℚ)/100,(1:ℚ)/25),((-19:ℚ)/100,(11:ℚ)/75)),(((857:ℚ)/6600,(-2927:ℚ)/39600),((-497:ℚ)/4400,(467:ℚ)/6600)),(((-7:ℚ)/100,(3:ℚ)/100),((-1:ℚ)/20,(1:ℚ)/100)),(((1:ℚ)/50,(-1:ℚ)/100),((-1:ℚ)/20,(1:ℚ)/50)),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((7:ℚ)/165,(-59:ℚ)/990),((-23:ℚ)/1100,(389:ℚ)/9900)),(((-3:ℚ)/50,(0:ℚ)),((-3:ℚ)/50,(0:ℚ))),(((-1:ℚ)/50,(0:ℚ)),((-9:ℚ)/200,(3:ℚ)/200)),(((-2:ℚ)/25,(1:ℚ)/50),((3:ℚ)/50,(0:ℚ))),(((-421:ℚ)/13200,(379:ℚ)/13200),((-2503:ℚ)/13200,(4001:ℚ)/39600)),(((-1:ℚ)/100,(0:ℚ)),((-1:ℚ)/20,(1:ℚ)/50)),(((0:ℚ),(-1:ℚ)/50),((1:ℚ)/50,(-1:ℚ)/25)),(((1:ℚ)/50,(0:ℚ)),((0:ℚ),(0:ℚ)))],![(((-871:ℚ)/13200,(-1651:ℚ)/39600),((-1429:ℚ)/13200,(241:ℚ)/7920)),(((-1027:ℚ)/6600,(-19:ℚ)/6600),((-251:ℚ)/3300,(163:ℚ)/1980)),(((103:ℚ)/600,(179:ℚ)/1800),((0:ℚ),(0:ℚ))),(((-1627:ℚ)/6600,(257:ℚ)/1584),((-221:ℚ)/4400,(409:ℚ)/19800)),(((-47:ℚ)/300,(89:ℚ)/900),((-127:ℚ)/1100,(673:ℚ)/9900)),(((-929:ℚ)/6600,(1477:ℚ)/19800),((3:ℚ)/50,(0:ℚ))),(((0:ℚ),(-1:ℚ)/100),((1:ℚ)/20,(-1:ℚ)/50)),(((1:ℚ)/50,(0:ℚ)),((0:ℚ),(0:ℚ))),(((-79:ℚ)/1100,(247:ℚ)/19800),((203:ℚ)/1650,(-1981:ℚ)/19800)),(((0:ℚ),(0:ℚ)),((1:ℚ)/50,(0:ℚ))),(((-3:ℚ)/50,(0:ℚ)),((3:ℚ)/50,(0:ℚ))),(((-3:ℚ)/50,(0:ℚ)),((-3:ℚ)/50,(0:ℚ))),(((-193:ℚ)/3300,(967:ℚ)/39600),((87:ℚ)/4400,(-71:ℚ)/4950)),(((0:ℚ),(0:ℚ)),((1:ℚ)/50,(0:ℚ))),(((-1:ℚ)/50,(0:ℚ)),((1:ℚ)/50,(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ)))],![(((-7:ℚ)/200,(13:ℚ)/200),((-1:ℚ)/8,(11:ℚ)/120)),(((-17:ℚ)/100,(1:ℚ)/25),((19:ℚ)/100,(-11:ℚ)/75)),(((-1627:ℚ)/6600,(257:ℚ)/1584),((221:ℚ)/4400,(-409:ℚ)/19800)),(((13:ℚ)/100,(9:ℚ)/100),((0:ℚ),(0:ℚ))),(((21:ℚ)/400,(-11:ℚ)/400),((33:ℚ)/400,(-17:ℚ)/400)),(((-797:ℚ)/6600,(1477:ℚ)/19800),((0:ℚ),(0:ℚ))),(((9:ℚ)/50,(-1:ℚ)/20),((-1:ℚ)/50,(0:ℚ))),(((-1:ℚ)/50,(0:ℚ)),((1:ℚ)/50,(0:ℚ))),(((137:ℚ)/2640,(-379:ℚ)/13200),((2239:ℚ)/13200,(-4001:ℚ)/39600)),(((-3:ℚ)/50,(0:ℚ)),((3:ℚ)/50,(0:ℚ))),(((1:ℚ)/50,(0:ℚ)),((0:ℚ),(0:ℚ))),(((-1:ℚ)/50,(0:ℚ)),((-1:ℚ)/50,(0:ℚ))),(((11:ℚ)/40,(-203:ℚ)/1200),((37:ℚ)/400,(-9:ℚ)/200)),(((2:ℚ)/25,(0:ℚ)),((-1:ℚ)/50,(0:ℚ))),(((-3:ℚ)/50,(0:ℚ)),((3:ℚ)/50,(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ)))],![(((-191:ℚ)/2640,(167:ℚ)/6600),((-437:ℚ)/6600,(2159:ℚ)/39600)),(((857:ℚ)/6600,(-2927:ℚ)/39600),((497:ℚ)/4400,(-467:ℚ)/6600)),(((-47:ℚ)/300,(89:ℚ)/900),((127:ℚ)/1100,(-673:ℚ)/9900)),(((21:ℚ)/400,(-11:ℚ)/400),((-33:ℚ)/400,(17:ℚ)/400)),(((7:ℚ)/100,(1:ℚ)/50),((0:ℚ),(0:ℚ))),(((-3:ℚ)/100,(1:ℚ)/100),((0:ℚ),(0:ℚ))),(((-1:ℚ)/20,(-1:ℚ)/100),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((-1:ℚ)/25,(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((1:ℚ)/25,(-1:ℚ)/50),((1:ℚ)/25,(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ)))],![(((-349:ℚ)/3300,(293:ℚ)/9900),((-112:ℚ)/825,(217:ℚ)/1980)),(((-7:ℚ)/100,(3:ℚ)/100),((1:ℚ)/20,(-1:ℚ)/100)),(((-929:ℚ)/6600,(1477:ℚ)/19800),((-3:ℚ)/50,(0:ℚ))),(((-797:ℚ)/6600,(1477:ℚ)/19800),((0:ℚ),(0:ℚ))),(((-3:ℚ)/100,(1:ℚ)/100),((0:ℚ),(0:ℚ))),(((127:ℚ)/3300,(131:ℚ)/3960),((0:ℚ),(0:ℚ))),(((-1:ℚ)/50,(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((523:ℚ)/13200,(-137:ℚ)/6600),((127:ℚ)/6600,(-533:ℚ)/39600)),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((1:ℚ)/50,(0:ℚ)),((1:ℚ)/25,(0:ℚ)))],![(((27:ℚ)/200,(-3:ℚ)/200),((3:ℚ)/200,(-1:ℚ)/40)),(((1:ℚ)/50,(-1:ℚ)/100),((1:ℚ)/20,(-1:ℚ)/50)),(((0:ℚ),(-1:ℚ)/100),((-1:ℚ)/20,(1:ℚ)/50)),(((9:ℚ)/50,(-1:ℚ)/20),((1:ℚ)/50,(0:ℚ))),(((-1:ℚ)/20,(-1:ℚ)/100),((0:ℚ),(0:ℚ))),(((-1:ℚ)/50,(0:ℚ)),((0:ℚ),(0:ℚ))),(((19:ℚ)/100,(1:ℚ)/100),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((-1:ℚ)/50,(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((-1:ℚ)/40,(-1:ℚ)/50),((2:ℚ)/25,(-9:ℚ)/200)),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ)))],![(((-3:ℚ)/200,(1:ℚ)/200),((3:ℚ)/200,(-3:ℚ)/200)),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((1:ℚ)/50,(0:ℚ)),((0:ℚ),(0:ℚ))),(((-1:ℚ)/50,(0:ℚ)),((-1:ℚ)/50,(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((9:ℚ)/100,(1:ℚ)/100),((0:ℚ),(0:ℚ))),(((0:ℚ),(-1:ℚ)/50),((1:ℚ)/25,(-1:ℚ)/50)),(((1:ℚ)/50,(0:ℚ)),((1:ℚ)/25,(0:ℚ))),(((-1:ℚ)/25,(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((-1:ℚ)/25,(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ)))],![(((53:ℚ)/300,(-89:ℚ)/900),((-353:ℚ)/2200,(1643:ℚ)/19800)),(((7:ℚ)/165,(-59:ℚ)/990),((23:ℚ)/1100,(-389:ℚ)/9900)),(((-79:ℚ)/1100,(247:ℚ)/19800),((-203:ℚ)/1650,(1981:ℚ)/19800)),(((137:ℚ)/2640,(-379:ℚ)/13200),((-2239:ℚ)/13200,(4001:ℚ)/39600)),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((523:ℚ)/13200,(-137:ℚ)/6600),((-127:ℚ)/6600,(533:ℚ)/39600)),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(-1:ℚ)/50),((-1:ℚ)/25,(1:ℚ)/50)),(((1211:ℚ)/6600,(-533:ℚ)/19800),((0:ℚ),(0:ℚ))),(((1:ℚ)/20,(-7:ℚ)/400),((9:ℚ)/400,(-1:ℚ)/100)),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(-3:ℚ)/100),((7:ℚ)/100,(-1:ℚ)/25))],![(((-17:ℚ)/400,(11:ℚ)/400),((13:ℚ)/400,(-9:ℚ)/400)),(((-3:ℚ)/50,(0:ℚ)),((3:ℚ)/50,(0:ℚ))),(((0:ℚ),(0:ℚ)),((-1:ℚ)/50,(0:ℚ))),(((-3:ℚ)/50,(0:ℚ)),((-3:ℚ)/50,(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((-1:ℚ)/50,(0:ℚ)),((0:ℚ),(0:ℚ))),(((1:ℚ)/50,(0:ℚ)),((-1:ℚ)/25,(0:ℚ))),(((1:ℚ)/20,(-7:ℚ)/400),((-9:ℚ)/400,(1:ℚ)/100)),(((-17:ℚ)/200,(13:ℚ)/100),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((-13:ℚ)/200,(1:ℚ)/50),((1:ℚ)/10,(-11:ℚ)/200)),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ)))],![(((-9:ℚ)/400,(-9:ℚ)/400),((11:ℚ)/400,(9:ℚ)/400)),(((-1:ℚ)/50,(0:ℚ)),((9:ℚ)/200,(-3:ℚ)/200)),(((-3:ℚ)/50,(0:ℚ)),((-3:ℚ)/50,(0:ℚ))),(((1:ℚ)/50,(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((-1:ℚ)/25,(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((1:ℚ)/20,(7:ℚ)/100),((0:ℚ),(0:ℚ))),(((1:ℚ)/50,(0:ℚ)),((0:ℚ),(0:ℚ))),(((3:ℚ)/200,(1:ℚ)/200),((3:ℚ)/200,(1:ℚ)/40)),(((-1:ℚ)/50,(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ)))],![(((1:ℚ)/20,(-3:ℚ)/100),((-1:ℚ)/20,(1:ℚ)/100)),(((-2:ℚ)/25,(1:ℚ)/50),((-3:ℚ)/50,(0:ℚ))),(((-3:ℚ)/50,(0:ℚ)),((3:ℚ)/50,(0:ℚ))),(((-1:ℚ)/50,(0:ℚ)),((1:ℚ)/50,(0:ℚ))),(((-1:ℚ)/25,(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((1:ℚ)/50,(0:ℚ)),((0:ℚ),(0:ℚ))),(((-3:ℚ)/25,(7:ℚ)/50),((0:ℚ),(0:ℚ))),(((-3:ℚ)/50,(1:ℚ)/50),((-1:ℚ)/10,(3:ℚ)/50)),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((1:ℚ)/50,(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ)))],![(((797:ℚ)/6600,(-1477:ℚ)/19800),((1:ℚ)/50,(0:ℚ))),(((-421:ℚ)/13200,(379:ℚ)/13200),((2503:ℚ)/13200,(-4001:ℚ)/39600)),(((-193:ℚ)/3300,(967:ℚ)/39600),((-87:ℚ)/4400,(71:ℚ)/4950)),(((11:ℚ)/40,(-203:ℚ)/1200),((-37:ℚ)/400,(9:ℚ)/200)),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((-1:ℚ)/40,(-1:ℚ)/50),((-2:ℚ)/25,(9:ℚ)/200)),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((-13:ℚ)/200,(1:ℚ)/50),((-1:ℚ)/10,(11:ℚ)/200)),(((3:ℚ)/200,(1:ℚ)/200),((-3:ℚ)/200,(-1:ℚ)/40)),(((-3:ℚ)/50,(1:ℚ)/50),((1:ℚ)/10,(-3:ℚ)/50)),(((-9:ℚ)/200,(19:ℚ)/200),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ)))],![(((9:ℚ)/200,(3:ℚ)/200),((7:ℚ)/200,(-1:ℚ)/40)),(((-1:ℚ)/100,(0:ℚ)),((1:ℚ)/20,(-1:ℚ)/50)),(((0:ℚ),(0:ℚ)),((-1:ℚ)/50,(0:ℚ))),(((2:ℚ)/25,(0:ℚ)),((1:ℚ)/50,(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((-1:ℚ)/25,(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((-1:ℚ)/50,(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((1:ℚ)/25,(3:ℚ)/50),((0:ℚ),(0:ℚ))),(((-1:ℚ)/50,(0:ℚ)),((0:ℚ),(0:ℚ))),(((-1:ℚ)/25,(0:ℚ)),((0:ℚ),(0:ℚ)))],![(((0:ℚ),(1:ℚ)/100),((-3:ℚ)/100,(1:ℚ)/50)),(((0:ℚ),(-1:ℚ)/50),((-1:ℚ)/50,(1:ℚ)/25)),(((-1:ℚ)/50,(0:ℚ)),((-1:ℚ)/50,(0:ℚ))),(((-3:ℚ)/50,(0:ℚ)),((-3:ℚ)/50,(0:ℚ))),(((1:ℚ)/25,(-1:ℚ)/50),((-1:ℚ)/25,(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((1:ℚ)/50,(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((-1:ℚ)/50,(0:ℚ)),((0:ℚ),(0:ℚ))),(((1:ℚ)/10,(1:ℚ)/50),((0:ℚ),(0:ℚ))),(((-1:ℚ)/25,(0:ℚ)),((0:ℚ),(0:ℚ)))],![(((-1:ℚ)/50,(1:ℚ)/100),((1:ℚ)/20,(-1:ℚ)/50)),(((1:ℚ)/50,(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((1:ℚ)/50,(0:ℚ)),((-1:ℚ)/25,(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(-3:ℚ)/100),((-7:ℚ)/100,(1:ℚ)/25)),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((0:ℚ),(0:ℚ)),((0:ℚ),(0:ℚ))),(((-1:ℚ)/25,(0:ℚ)),((0:ℚ),(0:ℚ))),(((-1:ℚ)/25,(0:ℚ)),((0:ℚ),(0:ℚ))),(((3:ℚ)/25,(0:ℚ)),((0:ℚ),(0:ℚ)))]]
def D (s : ℝ) (k : Fin 13) : ℝ := ((Draw k).1.1:ℝ)+((Draw k).1.2:ℝ)*s
def V (s : ℝ) : Matrix (Fin 16) (Fin 13) ℂ := fun i j => coeffVal s (Vraw i j)
def Q (s : ℝ) : Matrix (Fin 16) (Fin 16) ℂ := fun i j => coeffVal s (Qraw i j)
theorem raw_factor_row0 : ∀ j : Fin 16, Qraw 0 j =
    ∑ k : Fin 13, coeffMul (coeffMul (Vraw 0 k) (Draw k)) (coeffConj (Vraw j k)) := by
  decide +kernel
theorem raw_factor_row1 : ∀ j : Fin 16, Qraw 1 j =
    ∑ k : Fin 13, coeffMul (coeffMul (Vraw 1 k) (Draw k)) (coeffConj (Vraw j k)) := by
  decide +kernel
theorem raw_factor_row2 : ∀ j : Fin 16, Qraw 2 j =
    ∑ k : Fin 13, coeffMul (coeffMul (Vraw 2 k) (Draw k)) (coeffConj (Vraw j k)) := by
  decide +kernel
theorem raw_factor_row3 : ∀ j : Fin 16, Qraw 3 j =
    ∑ k : Fin 13, coeffMul (coeffMul (Vraw 3 k) (Draw k)) (coeffConj (Vraw j k)) := by
  decide +kernel
theorem raw_factor_row4 : ∀ j : Fin 16, Qraw 4 j =
    ∑ k : Fin 13, coeffMul (coeffMul (Vraw 4 k) (Draw k)) (coeffConj (Vraw j k)) := by
  decide +kernel
theorem raw_factor_row5 : ∀ j : Fin 16, Qraw 5 j =
    ∑ k : Fin 13, coeffMul (coeffMul (Vraw 5 k) (Draw k)) (coeffConj (Vraw j k)) := by
  decide +kernel
theorem raw_factor_row6 : ∀ j : Fin 16, Qraw 6 j =
    ∑ k : Fin 13, coeffMul (coeffMul (Vraw 6 k) (Draw k)) (coeffConj (Vraw j k)) := by
  decide +kernel
theorem raw_factor_row7 : ∀ j : Fin 16, Qraw 7 j =
    ∑ k : Fin 13, coeffMul (coeffMul (Vraw 7 k) (Draw k)) (coeffConj (Vraw j k)) := by
  decide +kernel
theorem raw_factor_row8 : ∀ j : Fin 16, Qraw 8 j =
    ∑ k : Fin 13, coeffMul (coeffMul (Vraw 8 k) (Draw k)) (coeffConj (Vraw j k)) := by
  decide +kernel
theorem raw_factor_row9 : ∀ j : Fin 16, Qraw 9 j =
    ∑ k : Fin 13, coeffMul (coeffMul (Vraw 9 k) (Draw k)) (coeffConj (Vraw j k)) := by
  decide +kernel
theorem raw_factor_row10 : ∀ j : Fin 16, Qraw 10 j =
    ∑ k : Fin 13, coeffMul (coeffMul (Vraw 10 k) (Draw k)) (coeffConj (Vraw j k)) := by
  decide +kernel
theorem raw_factor_row11 : ∀ j : Fin 16, Qraw 11 j =
    ∑ k : Fin 13, coeffMul (coeffMul (Vraw 11 k) (Draw k)) (coeffConj (Vraw j k)) := by
  decide +kernel
theorem raw_factor_row12 : ∀ j : Fin 16, Qraw 12 j =
    ∑ k : Fin 13, coeffMul (coeffMul (Vraw 12 k) (Draw k)) (coeffConj (Vraw j k)) := by
  decide +kernel
theorem raw_factor_row13 : ∀ j : Fin 16, Qraw 13 j =
    ∑ k : Fin 13, coeffMul (coeffMul (Vraw 13 k) (Draw k)) (coeffConj (Vraw j k)) := by
  decide +kernel
theorem raw_factor_row14 : ∀ j : Fin 16, Qraw 14 j =
    ∑ k : Fin 13, coeffMul (coeffMul (Vraw 14 k) (Draw k)) (coeffConj (Vraw j k)) := by
  decide +kernel
theorem raw_factor_row15 : ∀ j : Fin 16, Qraw 15 j =
    ∑ k : Fin 13, coeffMul (coeffMul (Vraw 15 k) (Draw k)) (coeffConj (Vraw j k)) := by
  decide +kernel

theorem word_table : ∀ i j : Fin 16,
    cycleReduce (inverseWord (words j) ++ words i) (rotations i j) = labels (momentIndex i j) := by
  decide

theorem objective_table : ∀ i : Fin 8,
    cycleReduce (objectiveWords i) (objectiveRotations i) = labels (objectiveIndex i) := by
  decide

theorem raw_factor : ∀ i j : Fin 16, Qraw i j =
    ∑ k : Fin 13, coeffMul (coeffMul (Vraw i k) (Draw k)) (coeffConj (Vraw j k)) := by
  intro i
  fin_cases i
  · exact raw_factor_row0
  · exact raw_factor_row1
  · exact raw_factor_row2
  · exact raw_factor_row3
  · exact raw_factor_row4
  · exact raw_factor_row5
  · exact raw_factor_row6
  · exact raw_factor_row7
  · exact raw_factor_row8
  · exact raw_factor_row9
  · exact raw_factor_row10
  · exact raw_factor_row11
  · exact raw_factor_row12
  · exact raw_factor_row13
  · exact raw_factor_row14
  · exact raw_factor_row15


theorem gram_factor (s : ℝ) (hs : s^2=3) :
    Q s = V s * Matrix.diagonal (fun j => (D s j : ℂ)) * (V s)ᴴ := by
  have hd (k : Fin 13) : coeffVal s (Draw k)=(D s k:ℂ) := by
    fin_cases k <;> apply Complex.ext <;> simp [coeffVal,D,Draw]
  ext i j
  have h := congrArg (coeffValHom s) (raw_factor i j)
  rw [map_sum] at h
  change coeffVal s (Qraw i j) = ∑ k : Fin 13,
    coeffVal s (coeffMul (coeffMul (Vraw i k) (Draw k)) (coeffConj (Vraw j k))) at h
  simp_rw [coeffVal_mul s hs,coeffVal_conj,hd] at h
  change coeffVal s (Qraw i j) = ∑ k : Fin 13,
    (V s * Matrix.diagonal (fun k => (D s k:ℂ))) i k * star (V s j k)
  simp only [Matrix.mul_diagonal,V]
  exact h

theorem root_bounds : (1732050807568 : ℝ)/1000000000000 < Real.sqrt 3 ∧
    Real.sqrt 3 < (1732050807569 : ℝ)/1000000000000 := by
  have hs : (Real.sqrt (3 : ℝ))^2=3 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  constructor <;> nlinarith

theorem D_positive (j : Fin 13) : 0 ≤ D (Real.sqrt 3) j := by
  have hl := root_bounds.1
  have hu := root_bounds.2
  fin_cases j <;> norm_num [D,Draw] <;> nlinarith only [hl,hu]

theorem Q_positive : (Q (Real.sqrt 3)).PosSemidef := by
  rw [gram_factor _ (Real.sq_sqrt (by norm_num))]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro j
  exact RCLike.nonneg_iff.mpr ⟨by simpa using D_positive j,by simp⟩

def beta (s : ℝ) : ℝ := 4/3+8*s/9
def objectiveCoeff (s : ℝ) : Fin 8 → ℂ :=
  ![⟨1/2,-s/6⟩,⟨1/2,-s/6⟩,⟨1/2,-s/6⟩,⟨-1/2,-s/6⟩,
    ⟨1/2,s/6⟩,⟨1/2,s/6⟩,⟨1/2,s/6⟩,⟨-1/2,s/6⟩]
theorem coefficient_identity (s : ℝ) (t : Fin 113 → ℂ) :
    (beta s : ℂ) * t 0 - (∑ k : Fin 8, objectiveCoeff s k * t (objectiveIndex k)) =
      ∑ i : Fin 16, ∑ j : Fin 16, Q s i j * t (momentIndex i j) := by
  apply Complex.ext <;>
    norm_num [Q,Qraw,coeffVal,beta,objectiveCoeff,objectiveIndex,momentIndex,Fin.sum_univ_succ,
      Complex.mul_re,Complex.mul_im] <;> ring

#print axioms Q_positive
#print axioms coefficient_identity
end
end CGLMP3SOS


namespace CGLMP3SOS
noncomputable section
open scoped Matrix ComplexOrder
abbrev M3 := Matrix (Fin 3) (Fin 3) ℂ
abbrev U3 := Matrix.unitaryGroup (Fin 3) ℂ
def κ : ℂ := ⟨1,-Real.sqrt 3/3⟩
def γ : ℂ := ⟨-1,-Real.sqrt 3/3⟩
def tr (g : U3) : ℂ := Matrix.trace (g:M3)/3

theorem tr_one : tr (1:U3)=1 := by
  norm_num [tr,Matrix.trace,Fin.sum_univ_succ]

theorem tr_cycle (g h : U3) : tr (g*h)=tr (h*g) := by
  change Matrix.trace ((g:M3)*(h:M3))/3=Matrix.trace ((h:M3)*(g:M3))/3
  rw [Matrix.trace_mul_comm]

theorem tr_inverse (g : U3) : tr g⁻¹=star (tr g) := by
  change Matrix.trace (g:M3)ᴴ/3=star (Matrix.trace (g:M3)/3)
  simp [Matrix.trace_conjTranspose]

def pairing (A : Matrix (Fin 16) (Fin 16) ℂ) (w : Fin 16 → M3) : ℂ :=
  ∑ i : Fin 16, ∑ j : Fin 16, A i j * (Matrix.trace ((w j)ᴴ*w i)/3)

theorem pairing_nonneg (A : Matrix (Fin 16) (Fin 16) ℂ) (hA : A.PosSemidef)
    (w : Fin 16 → M3) : 0 ≤ (pairing A w).re := by
  have hswap (f : Fin 16 → Fin 16 → Fin 3 → Fin 3 → ℂ) :
      (∑ i : Fin 16, ∑ j : Fin 16, ∑ a : Fin 3, ∑ b : Fin 3, f i j a b) =
        ∑ a : Fin 3, ∑ b : Fin 3, ∑ i : Fin 16, ∑ j : Fin 16, f i j a b := by
    calc
      _ = ∑ p : Fin 16 × Fin 16, ∑ q : Fin 3 × Fin 3, f p.1 p.2 q.1 q.2 := by
        simp only [Fintype.sum_prod_type]
      _ = ∑ q : Fin 3 × Fin 3, ∑ p : Fin 16 × Fin 16, f p.1 p.2 q.1 q.2 := Finset.sum_comm
      _ = _ := by simp only [Fintype.sum_prod_type]
  have heq : pairing A w =
      (∑ a : Fin 3, ∑ b : Fin 3, ∑ i : Fin 16, ∑ j : Fin 16,
        w i b a * A i j * star (w j b a))/3 := by
    unfold pairing
    simp only [←mul_div_assoc,←Finset.sum_div]
    congr 1
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply]
    simp_rw [Finset.mul_sum]
    rw [hswap]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hnonneg : 0 ≤ (∑ a : Fin 3, ∑ b : Fin 3, ∑ i : Fin 16, ∑ j : Fin 16,
      w i b a * A i j * star (w j b a)).re := by
    rw [←Complex.coe_reAddGroupHom]
    rw [map_sum]
    apply Finset.sum_nonneg
    intro a ha
    rw [map_sum]
    apply Finset.sum_nonneg
    intro b hb
    have h := hA.re_dotProduct_nonneg (fun i => star (w i b a))
    simpa [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc] using h
  rw [heq]
  simpa using div_nonneg hnonneg (by norm_num : (0:ℝ) ≤ 3)


#print axioms pairing_nonneg
end
end CGLMP3SOS


namespace CGLMP3SOS
noncomputable section
open scoped Matrix ComplexOrder
def bellTrace (u : Fin 4 → U3) : ℂ :=
  ∑ k : Fin 8, objectiveCoeff (Real.sqrt 3) k * tr (eval u (objectiveWords k))

theorem sos_identity (u : Fin 4 → U3) (hu : ∀ i,(u i)^3=1) :
    (beta (Real.sqrt 3):ℂ)-bellTrace u =
      pairing (Q (Real.sqrt 3)) (fun i => ((eval u (words i):U3):M3)) := by
  have h := coefficient_identity (Real.sqrt 3) (fun i => tr (eval u (labels i)))
  have hm : ∀ i j : Fin 16, tr (eval u (labels (momentIndex i j)))=
      Matrix.trace ((((eval u (words j):U3):M3)ᴴ)*((eval u (words i):U3):M3))/3 := by
    intro i j
    have he := trace_cycleReduce u hu tr tr_cycle
      (inverseWord (words j)++words i) (rotations i j)
    rw [word_table,eval_append,eval_inverseWord u hu] at he
    exact he
  have ho : ∀ i : Fin 8, tr (eval u (labels (objectiveIndex i)))=tr (eval u (objectiveWords i)) := by
    intro i
    have he := trace_cycleReduce u hu tr tr_cycle (objectiveWords i) (objectiveRotations i)
    rwa [objective_table] at he
  simp_rw [hm,ho] at h
  have hzero : tr (eval u (labels 0))=1 := by simpa [labels,eval] using tr_one
  simpa only [hzero,mul_one,bellTrace,pairing] using h

theorem tracial_bell_bound (u : Fin 4 → U3) (hu : ∀ i,(u i)^3=1) :
    (bellTrace u).re ≤ beta (Real.sqrt 3) := by
  have hn := pairing_nonneg _ Q_positive (fun i => ((eval u (words i):U3):M3))
  rw [←sos_identity u hu] at hn
  simpa only [Complex.sub_re,Complex.ofReal_re,sub_nonneg] using hn

def correlation (u : Fin 4 → U3) : ℝ :=
  (κ*tr (u 0*(u 2)⁻¹)+κ*tr (u 2*(u 1)⁻¹)+κ*tr (u 1*(u 3)⁻¹)+γ*tr (u 3*(u 0)⁻¹)).re

theorem bellTrace_correlation (u : Fin 4 → U3) (hu : ∀ i,(u i)^3=1) :
    (bellTrace u).re=correlation u := by
  have hpow (i : Fin 4) : (u i)^2=(u i)⁻¹ := by
    simpa [invExp] using pow_invExp (u i) (hu i) (1:Fin 3)
  have hi0 : tr (u 2*(u 0)⁻¹)=star (tr (u 0*(u 2)⁻¹)) := by
    simpa only [mul_inv_rev,inv_inv] using tr_inverse (u 0*(u 2)⁻¹)
  have hi1 : tr (u 1*(u 2)⁻¹)=star (tr (u 2*(u 1)⁻¹)) := by
    simpa only [mul_inv_rev,inv_inv] using tr_inverse (u 2*(u 1)⁻¹)
  have hi2 : tr (u 3*(u 1)⁻¹)=star (tr (u 1*(u 3)⁻¹)) := by
    simpa only [mul_inv_rev,inv_inv] using tr_inverse (u 1*(u 3)⁻¹)
  have hi3 : tr (u 0*(u 3)⁻¹)=star (tr (u 3*(u 0)⁻¹)) := by
    simpa only [mul_inv_rev,inv_inv] using tr_inverse (u 3*(u 0)⁻¹)
  norm_num [bellTrace,objectiveCoeff,objectiveWords,eval,Fin.sum_univ_succ,hpow]
  rw [hi0,hi1,hi2,hi3]
  simp [correlation,κ,γ,Complex.mul_re,Complex.mul_im]
  ring

theorem unitary_cubic_bound (u : Fin 4 → U3) (hu : ∀ i,(u i)^3=1) :
    correlation u ≤ beta (Real.sqrt 3) := by
  rw [←bellTrace_correlation u hu]
  exact tracial_bell_bound u hu

#print axioms tracial_bell_bound
#print axioms unitary_cubic_bound
end
end CGLMP3SOS


namespace CGLMP3SOS
noncomputable section
open scoped Matrix
set_option maxHeartbeats 0
def phase : ℂ := ⟨-1/2,-Real.sqrt 3/2⟩
def K (u : U3) : U3 := CGLMP3Global.Z*u*CGLMP3Global.Z⁻¹*u⁻¹
def observable (E : U3) : U3 := E*CGLMP3Global.Z*E⁻¹

theorem clock_cube : CGLMP3Global.Z^3=1 := by
  apply Subtype.ext
  change CGLMP3Global.clock^3=(1:M3)
  have hs : (Real.sqrt (3:ℝ))^2=3 := Real.sq_sqrt (by norm_num)
  have h3 : (Real.sqrt (3:ℝ))^3=3*Real.sqrt 3 := by
    calc
      _ = (Real.sqrt (3:ℝ))^2*Real.sqrt 3 := by ring
      _ = _ := by rw [hs]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [CGLMP3Global.clock,CGLMP3Trace.clock,pow_succ,Matrix.mul_apply,
      Fin.sum_univ_succ,Complex.mul_re,Complex.mul_im] <;>
    ring_nf <;> simp only [hs,h3] <;> norm_num <;> ring

theorem observable_cube (E : U3) : (observable E)^3=1 := by
  calc
    _ = E*CGLMP3Global.Z^3*E⁻¹ := by
      unfold observable
      simp only [pow_succ,pow_zero,mul_one]
      group
    _ = 1 := by rw [clock_cube]; group

theorem tr_conjugation (E g : U3) : tr (E*g*E⁻¹)=tr g := by
  rw [tr_cycle]
  congr 1
  group

theorem relative_trace (E F : U3) :
    tr (K (E⁻¹*F))=tr (observable E*(observable F)⁻¹) := by
  have h : observable E*(observable F)⁻¹=E*K (E⁻¹*F)*E⁻¹ := by
    unfold observable K
    group
  rw [h,tr_conjugation]

theorem cost_K (u : U3) : CGLMP3Physical.cost u=1-(κ*tr (K u)).re := by
  have h := CGLMP3Integration.physical_cost_trace u u.property
  change CGLMP3Physical.cost u=1-(Matrix.trace (K u:M3)).re/3-
    (Matrix.trace (K u:M3)).im/(3*Real.sqrt 3) at h
  rw [h]
  have hs : (Real.sqrt (3:ℝ))^2=3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt (3:ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hfrac (x : ℝ) : x/(3*Real.sqrt 3)=Real.sqrt 3*x/9 := by
    field_simp
    rw [hs]
    ring
  rw [hfrac]
  simp [κ,tr,Complex.mul_re,Complex.div_re]
  ring

theorem shift_clock_phase :
    (CGLMP3Global.shift * CGLMP3Global.clockᴴ * CGLMP3Global.shiftᴴ : M3) =
      phase • CGLMP3Global.clockᴴ := by
  have hs : (Real.sqrt (3:ℝ))^2=3 := Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [CGLMP3Global.shift,CGLMP3Physical.shift,CGLMP3Global.clock,CGLMP3Trace.clock,
      phase,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_succ,
      Complex.mul_re,Complex.mul_im] <;> nlinarith [hs]

theorem K_shift (u : U3) : (K (u*CGLMP3Global.S):M3)=phase • (K u:M3) := by
  change CGLMP3Global.clock*((u:M3)*CGLMP3Global.shift)*CGLMP3Global.clockᴴ*
    ((u:M3)*CGLMP3Global.shift)ᴴ = phase • (K u:M3)
  rw [Matrix.conjTranspose_mul]
  calc
    _ = CGLMP3Global.clock*(u:M3)*
      (CGLMP3Global.shift*CGLMP3Global.clockᴴ*CGLMP3Global.shiftᴴ)*(u:M3)ᴴ := by noncomm_ring
    _ = _ := by rw [shift_clock_phase]; simp [Matrix.mul_smul,Matrix.smul_mul]; rfl

theorem tr_K_shift (u : U3) : tr (K (u*CGLMP3Global.S))=phase*tr (K u) := by
  change Matrix.trace (K (u*CGLMP3Global.S):M3)/3=phase*(Matrix.trace (K u:M3)/3)
  rw [K_shift,Matrix.trace_smul]
  simp only [smul_eq_mul]
  ring

theorem kappa_phase : κ*phase=γ := by
  have hs : (Real.sqrt (3:ℝ))^2=3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> norm_num [κ,phase,γ,Complex.mul_re,Complex.mul_im] <;> nlinarith [hs]

def correlationBell (E₀ E₁ F₀ F₁ : U3) : ℝ :=
  (κ*tr (observable E₀*(observable F₀)⁻¹)+
    κ*tr (observable F₀*(observable E₁)⁻¹)+
    κ*tr (observable E₁*(observable F₁)⁻¹)+
    γ*tr (observable F₁*(observable E₀)⁻¹)).re

theorem physical_correlation (E₀ E₁ F₀ F₁ : U3) :
    4-CGLMP3Physical.bellCost E₀ E₁ F₀ F₁=correlationBell E₀ E₁ F₀ F₁ := by
  rw [CGLMP3Physical.physical_cost_factorization]
  change 4-(CGLMP3Physical.cost (E₀⁻¹*F₀:U3)+CGLMP3Physical.cost (F₀⁻¹*E₁:U3)+
    CGLMP3Physical.cost (E₁⁻¹*F₁:U3)+CGLMP3Physical.cost (F₁⁻¹*E₀*CGLMP3Global.S:U3))= _
  simp only [cost_K, tr_K_shift,←mul_assoc,kappa_phase,relative_trace]
  simp [correlationBell]
  ring

#print axioms physical_correlation
end
end CGLMP3SOS


namespace CGLMP3SOS
noncomputable section
def measurements (E₀ E₁ F₀ F₁ : U3) : Fin 4 → U3 :=
  ![observable E₀,observable E₁,observable F₀,observable F₁]

theorem beta_normalization : beta (Real.sqrt 3)=(4:ℝ)/3+8/(3*Real.sqrt 3) := by
  have hs : (Real.sqrt (3:ℝ))^2=3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt (3:ℝ) := Real.sqrt_pos.2 (by norm_num)
  unfold beta
  field_simp
  nlinarith [hs]

theorem effective_global_bound (E₀ E₁ F₀ F₁ : U3) :
    4-CGLMP3Physical.bellCost E₀ E₁ F₀ F₁ ≤ (4:ℝ)/3+8/(3*Real.sqrt 3) := by
  have hcube : ∀ i : Fin 4, (measurements E₀ E₁ F₀ F₁ i)^3=1 := by
    intro i
    fin_cases i <;> simpa [measurements] using observable_cube _
  have h := unitary_cubic_bound (measurements E₀ E₁ F₀ F₁) hcube
  have heq : correlation (measurements E₀ E₁ F₀ F₁)=correlationBell E₀ E₁ F₀ F₁ := by
    simp [correlation,measurements,correlationBell]
  rw [heq,beta_normalization] at h
  rw [physical_correlation]
  exact h

/-- Unconditional physical global bound: no analytic certificate or angular-budget hypothesis. -/
theorem actual_global_bound (A₀ A₁ B₀ B₁ : U3) :
    CGLMP3Integration.actualBellValue A₀ A₁ B₀ B₁ ≤ (4:ℝ)/3+8/(3*Real.sqrt 3) := by
  let E₀ : U3 := ⟨CGLMP3Physical.conjugateBasis A₀,
    CGLMP3Physical.conjugateBasis_unitary A₀ A₀.property⟩
  let E₁ : U3 := ⟨CGLMP3Physical.conjugateBasis A₁,
    CGLMP3Physical.conjugateBasis_unitary A₁ A₁.property⟩
  have h := effective_global_bound E₀ E₁ B₀ B₁
  simpa only [CGLMP3Integration.actualBellValue,CGLMP3Physical.born_eq_effective,
    CGLMP3Physical.bellCost] using h

/-- The fixed-state qutrit CGLMP value is globally bounded, and the bound is attained. -/
theorem full_global_optimality :
    (∀ A₀ A₁ B₀ B₁ : U3,
      CGLMP3Integration.actualBellValue A₀ A₁ B₀ B₁ ≤ (4:ℝ)/3+8/(3*Real.sqrt 3)) ∧
    (∃ A₀ A₁ B₀ B₁ : U3,
      CGLMP3Integration.actualBellValue A₀ A₁ B₀ B₁ = (4:ℝ)/3+8/(3*Real.sqrt 3)) := by
  refine ⟨actual_global_bound,?_⟩
  obtain ⟨h0,h1,h2,h3,hval⟩ := CGLMP3Integration.actual_measurement_attainment
  refine ⟨⟨CGLMP3Physical.conjugateBasis (1:M3),h0⟩,
    ⟨CGLMP3Physical.conjugateBasis (CGLMP3Concrete.Q^2),h1⟩,
    ⟨CGLMP3Concrete.Q,h2⟩,⟨CGLMP3Concrete.Q^3,h3⟩,hval⟩

#print axioms actual_global_bound
#print axioms full_global_optimality
#check full_global_optimality
end
end CGLMP3SOS
