import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.Module.LinearMap

noncomputable section

open Filter

open scoped BigOperators
open scoped Topology

/--
A Schauder basis of a Banach space.

The sequence `basis` is a Schauder basis when every vector `x` has a unique
norm-convergent expansion
`∑' n, coeff n x • basis n = x`.  The coordinate maps are bundled as
continuous linear maps, which is the natural Banach-space formulation.
-/
structure SchauderBasis (𝕜 E : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] where
  /-- The basis vectors. -/
  basis : ℕ → E
  /-- The continuous coordinate functionals. -/
  coeff : ℕ → E →L[𝕜] 𝕜
  /-- Every vector is the sum of its basis expansion. -/
  hasSum_repr : ∀ x : E, HasSum (fun n : ℕ => coeff n x • basis n) x
  /-- The coefficients in such an expansion are unique. -/
  unique_coeff :
    ∀ (x : E) (a : ℕ → 𝕜), HasSum (fun n : ℕ => a n • basis n) x →
      a = fun n : ℕ => coeff n x

namespace SchauderBasis

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- The `n`th coordinate of `x` with respect to a Schauder basis. -/
def coord (b : SchauderBasis 𝕜 E) (n : ℕ) (x : E) : 𝕜 :=
  b.coeff n x

@[simp]
theorem hasSum_repr_apply (b : SchauderBasis 𝕜 E) (x : E) :
    HasSum (fun n : ℕ => b.coeff n x • b.basis n) x :=
  b.hasSum_repr x

/--
A Schauder basis is unconditional if every basis expansion converges to the
same vector after any permutation of its terms.
-/
def IsUnconditional (b : SchauderBasis 𝕜 E) : Prop :=
  ∀ (x : E) (σ : Equiv.Perm ℕ),
    HasSum (fun n : ℕ => b.coeff (σ n) x • b.basis (σ n)) x

end SchauderBasis

/--
An unconditional Schauder basis of a Banach space.

This bundles a Schauder basis together with the assertion that all rearranged
basis expansions converge to the same vector.
-/
structure UnconditionalSchauderBasis (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] where
  /-- The underlying Schauder basis. -/
  toSchauderBasis : SchauderBasis ℂ E
  /-- Unconditional convergence of every basis expansion. -/
  unconditional : toSchauderBasis.IsUnconditional




namespace UnconditionalSchauderBasis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

instance : Coe (UnconditionalSchauderBasis E) (SchauderBasis ℂ E) where
  coe b := b.toSchauderBasis

/-- The basis vectors of an unconditional Schauder basis. -/
def basis (b : UnconditionalSchauderBasis E) : ℕ → E :=
  b.toSchauderBasis.basis

/-- The continuous coordinate functionals of an unconditional Schauder basis. -/
def coeff (b : UnconditionalSchauderBasis E) : ℕ → E →L[ℂ] ℂ :=
  b.toSchauderBasis.coeff

@[simp]
theorem hasSum_repr_apply (b : UnconditionalSchauderBasis E) (x : E) :
    HasSum (fun n : ℕ => b.coeff n x • b.basis n) x :=
  b.toSchauderBasis.hasSum_repr x

theorem hasSum_rearranged (b : UnconditionalSchauderBasis E)
    (x : E) (σ : Equiv.Perm ℕ) :
    HasSum (fun n : ℕ => b.coeff (σ n) x • b.basis (σ n)) x :=
  b.unconditional x σ

end UnconditionalSchauderBasis

/-!
## From a finite sign estimate to an unconditional Schauder basis

The next definitions are intended for the criterion discussed in the chat.
They are written in the notation of this file, namely for complex Banach
spaces and sequences indexed by `ℕ`.

Mathematically, the theorem is:

* if `x : ℕ → E` has dense closed linear span,
* if no `x n` is zero,
* and if finite signed sums satisfy
  `‖∑ i ∈ s, (ε i * a i) • x i‖ ≤ C * ‖∑ i ∈ s, a i • x i‖`,

then `x` determines an unconditional Schauder basis.

The finite-dimensional algebraic parts below have been separated from the
functional-analytic construction of the coordinate functionals. The latter is
left as the main `sorry`, because it requires building continuous coordinate
maps on the algebraic span and extending them by density.
-/

namespace UnconditionalCriterion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/--
The closed complex linear span of the sequence `x` is all of `E`.

This is the correct Banach-space interpretation of "the vectors `x n` span
`E`" when the space may be infinite-dimensional.
-/
def HasDenseSpan (x : ℕ → E) : Prop :=
  closure ((Submodule.span ℂ (Set.range x) : Submodule ℂ E) : Set E) = Set.univ

/--
Finite signed unconditionality estimate.

This is the Lean version of

`‖∑_{i ∈ s} ε_i a_i x_i‖ ≤ C ‖∑_{i ∈ s} a_i x_i‖`,

where each `ε_i` is either `1` or `-1`.
-/
def HasFiniteSignBound (x : ℕ → E) (C : ℝ) : Prop :=
  ∀ (s : Finset ℕ) (a ε : ℕ → ℂ),
    (∀ i ∈ s, ε i = 1 ∨ ε i = -1) →
      ‖∑ i ∈ s, (ε i * a i) • x i‖
        ≤ C * ‖∑ i ∈ s, a i • x i‖

/--
A useful intermediate package: a sequence together with already constructed
continuous coordinate maps and unconditional convergence of the expansions.

This is often easier to construct first; the conversion to
`UnconditionalSchauderBasis` is immediate.
-/
structure SchauderData (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] where
  /-- The basis vectors. -/
  basis : ℕ → E
  /-- The continuous coordinate functionals. -/
  coeff : ℕ → E →L[ℂ] ℂ
  /-- Every vector is the sum of its basis expansion. -/
  hasSum_repr : ∀ x : E, HasSum (fun n : ℕ => coeff n x • basis n) x
  /-- The coefficients in such an expansion are unique. -/
  unique_coeff :
    ∀ (x : E) (a : ℕ → ℂ), HasSum (fun n : ℕ => a n • basis n) x →
      a = fun n : ℕ => coeff n x
  /-- Every rearranged basis expansion has the same sum. -/
  unconditional :
    ∀ (x : E) (σ : Equiv.Perm ℕ),
      HasSum (fun n : ℕ => coeff (σ n) x • basis (σ n)) x

/-- Convert the intermediate package into the structure used in this file. -/
def SchauderData.toUnconditionalSchauderBasis
    (d : SchauderData E) :
    UnconditionalSchauderBasis E :=
{
  toSchauderBasis :=
  {
    basis := d.basis
    coeff := d.coeff
    hasSum_repr := d.hasSum_repr
    unique_coeff := d.unique_coeff
  }
  unconditional := d.unconditional
}

/--
The signs equal to `1` on `t` and to `-1` outside `t`.

In applications this is used only on a finite set `s`, with `t ⊆ s`.
-/
def projectionSigns (t : Finset ℕ) : ℕ → ℂ :=
  fun i => if i ∈ t then 1 else -1

@[simp]
lemma projectionSigns_of_mem (t : Finset ℕ) {i : ℕ} (hi : i ∈ t) :
    projectionSigns t i = 1 := by
  simp [projectionSigns, hi]

@[simp]
lemma projectionSigns_of_not_mem (t : Finset ℕ) {i : ℕ} (hi : i ∉ t) :
    projectionSigns t i = -1 := by
  simp [projectionSigns, hi]

lemma projectionSigns_is_sign (s t : Finset ℕ) :
    ∀ i ∈ s, projectionSigns t i = 1 ∨ projectionSigns t i = -1 := by
  intro i _hi
  by_cases hit : i ∈ t
  · left
    simp [projectionSigns, hit]
  · right
    simp [projectionSigns, hit]

/--
Algebraic identity behind the projection estimate.

With signs `+1` on `t` and `-1` on `s \ t`, the signed sum is
`2` times the projection onto `t`, minus the original sum.
-/
lemma signed_sum_eq_two_projection_sub_sum
    (x : ℕ → E)
    (s t : Finset ℕ)
    (hts : t ⊆ s)
    (a : ℕ → ℂ) :
    (∑ i ∈ s, (projectionSigns t i * a i) • x i)
      =
    (2 : ℂ) • (∑ i ∈ t, a i • x i)
      -
    (∑ i ∈ s, a i • x i) := by
  classical
  have hproj :
      (∑ i ∈ s, (((if i ∈ t then (2 : ℂ) else 0) * a i) • x i))
        = (2 : ℂ) • (∑ i ∈ t, a i • x i) := by
    calc
      (∑ i ∈ s, (((if i ∈ t then (2 : ℂ) else 0) * a i) • x i))
          = ∑ i ∈ t, (((if i ∈ t then (2 : ℂ) else 0) * a i) • x i) := by
            exact (Finset.sum_subset
              (s₁ := t) (s₂ := s)
              (f := fun i => (((if i ∈ t then (2 : ℂ) else 0) * a i) • x i))
              hts (by
                intro i _his hit
                simp [hit])).symm
      _ = ∑ i ∈ t, ((2 : ℂ) * a i) • x i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [hi]
      _ = (2 : ℂ) • (∑ i ∈ t, a i • x i) := by
            rw [Finset.smul_sum]
            change (∑ i ∈ t, ((2 : ℂ) * a i) • x i)
              = ∑ i ∈ t, (2 : ℂ) • (a i • x i)
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [mul_smul]
  rw [← hproj, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  by_cases hit : i ∈ t
  · rw [projectionSigns_of_mem t hit]
    simp only [one_mul]
    rw [← sub_smul]
    congr 1
    simp [hit]
    ring
  · rw [projectionSigns_of_not_mem t hit]
    simp [hit, neg_smul]

/--
The finite sign estimate implies uniform boundedness of all finite coordinate
projections.

Mathematically, this is the estimate

`‖∑ i ∈ t, a i • x i‖ ≤ ((C + 1) / 2) * ‖∑ i ∈ s, a i • x i‖`

whenever `t ⊆ s`.
-/
lemma finite_projection_bound_of_sign_bound
    (x : ℕ → E)
    (C : ℝ)
    (hC : 0 ≤ C)
    (h_sign : HasFiniteSignBound x C)
    (s t : Finset ℕ)
    (hts : t ⊆ s)
    (a : ℕ → ℂ) :
    ‖∑ i ∈ t, a i • x i‖
      ≤ ((C + 1) / 2) * ‖∑ i ∈ s, a i • x i‖ := by
  classical
  have _hC_plus_one : 0 ≤ C + 1 := add_nonneg hC zero_le_one
  let p : E := ∑ i ∈ t, a i • x i
  let y : E := ∑ i ∈ s, a i • x i
  let z : E := ∑ i ∈ s, (projectionSigns t i * a i) • x i
  have hz_bound : ‖z‖ ≤ C * ‖y‖ := by
    simpa [z, y] using h_sign s a (projectionSigns t) (projectionSigns_is_sign s t)
  have hz_eq : z = (2 : ℂ) • p - y := by
    simpa [z, p, y] using signed_sum_eq_two_projection_sub_sum x s t hts a
  have hp_eq : p = ((2 : ℂ)⁻¹) • (z + y) := by
    rw [hz_eq]
    simp [p, sub_add_cancel]
  have hhalf : ‖((2 : ℂ)⁻¹)‖ = (1 / 2 : ℝ) := by
    norm_num [Complex.normSq, Complex.normSq_apply]
  have hnorm :
      ‖p‖ ≤ (1 / 2 : ℝ) * (‖z‖ + ‖y‖) := by
    calc
      ‖p‖ = ‖((2 : ℂ)⁻¹) • (z + y)‖ := by rw [hp_eq]
      _ = (1 / 2 : ℝ) * ‖z + y‖ := by
            rw [norm_smul, hhalf]
      _ ≤ (1 / 2 : ℝ) * (‖z‖ + ‖y‖) := by
            exact mul_le_mul_of_nonneg_left (norm_add_le z y) (by norm_num)
  have hzy : ‖z‖ + ‖y‖ ≤ (C + 1) * ‖y‖ := by
    calc
      ‖z‖ + ‖y‖ ≤ C * ‖y‖ + ‖y‖ := by
        exact add_le_add hz_bound le_rfl
      _ = (C + 1) * ‖y‖ := by ring
  have hmain : ‖p‖ ≤ ((C + 1) / 2) * ‖y‖ := by
    calc
      ‖p‖ ≤ (1 / 2 : ℝ) * (‖z‖ + ‖y‖) := hnorm
      _ ≤ (1 / 2 : ℝ) * ((C + 1) * ‖y‖) := by
            exact mul_le_mul_of_nonneg_left hzy (by norm_num)
      _ = ((C + 1) / 2) * ‖y‖ := by ring
  simpa [p, y] using hmain

/--
Uniform boundedness of all finite coordinate projections for the sequence `x`.

The estimate is stated only on finite sums: if `t ⊆ s`, then the partial sum
over `t` is bounded by `K` times the partial sum over `s`.
-/
def FiniteProjectionBound (x : ℕ → E) (K : ℝ) : Prop :=
  ∀ (s t : Finset ℕ), t ⊆ s → ∀ a : ℕ → ℂ,
    ‖∑ i ∈ t, a i • x i‖ ≤ K * ‖∑ i ∈ s, a i • x i‖

/-- The finite sign estimate gives the uniform finite projection bound. -/
lemma finiteProjectionBound_of_signBound
    (x : ℕ → E)
    (C : ℝ)
    (hC : 0 ≤ C)
    (h_sign : HasFiniteSignBound x C) :
    FiniteProjectionBound x ((C + 1) / 2) := by
  intro s t hts a
  exact finite_projection_bound_of_sign_bound x C hC h_sign s t hts a

/--
The singleton and finite-projection estimates imply finite linear independence
of the sequence.

This is the first genuinely algebraic construction step after the projection
bound. It is separated so later coordinate-map construction can depend on a
clean `LinearIndependent` hypothesis.
-/
lemma linearIndependent_of_finiteProjectionBound
    (x : ℕ → E)
    (hx_ne : ∀ n, x n ≠ 0)
    (K : ℝ)
    (h_proj : FiniteProjectionBound x K) :
    LinearIndependent ℂ x := by
  classical
  rw [linearIndependent_iff']
  intro s a hsum i hi
  have hsingleton :
      ‖∑ j ∈ ({i} : Finset ℕ), a j • x j‖ ≤ K * ‖∑ j ∈ s, a j • x j‖ :=
    h_proj s ({i} : Finset ℕ) (by
      intro j hj
      have hji : j = i := by simpa using hj
      simpa [hji] using hi) a
  have hsingleton_zero : ∑ j ∈ ({i} : Finset ℕ), a j • x j = 0 := by
    have hnorm_le_zero : ‖∑ j ∈ ({i} : Finset ℕ), a j • x j‖ ≤ 0 := by
      simpa [hsum] using hsingleton
    exact norm_eq_zero.mp (le_antisymm hnorm_le_zero (norm_nonneg _))
  have hai_smul : a i • x i = 0 := by
    simpa using hsingleton_zero
  exact (smul_eq_zero.mp hai_smul).resolve_right (hx_ne i)

/--
The coordinate maps agree with the finite-dimensional coordinate projections:
if `n ≤ k`, then the `n`th coordinate of a vector in
`span {x 0, ..., x k}` is its `n`th coefficient.
-/
def CoordMapsAgreeOnFiniteSpans
    (x : ℕ → E) (coeff : ℕ → E →L[ℂ] ℂ) : Prop :=
  ∀ (s : Finset ℕ) (a : ℕ → ℂ) (n : ℕ),
    coeff n (∑ i ∈ s, a i • x i) = if n ∈ s then a n else 0

/--
Coordinate maps obtained from the finite-dimensional coordinates on the
algebraic span and extended continuously to `E`.
-/
lemma exists_coordMaps_of_finiteProjectionBound
    (x : ℕ → E)
    (hx_dense : HasDenseSpan x)
    (h_li : LinearIndependent ℂ x)
    (K : ℝ)
    (h_proj : FiniteProjectionBound x K) :
    ∃ coeff : ℕ → E →L[ℂ] ℂ, CoordMapsAgreeOnFiniteSpans x coeff := by
  classical
  let S : Submodule ℂ E := Submodule.span ℂ (Set.range x)
  let e : S →ₗ[ℂ] E := Submodule.subtype S
  let coordLin : ℕ → S →ₗ[ℂ] ℂ :=
    fun n => (Finsupp.lapply n : (ℕ →₀ ℂ) →ₗ[ℂ] ℂ).comp h_li.repr
  have h_dense : DenseRange e := by
    rw [denseRange_iff_closure_range]
    simpa [HasDenseSpan, S, e, LinearMap.range_eq_map, Submodule.range_subtype] using hx_dense
  have h_norm : ∀ n, ∃ C : ℝ, ∀ y : S, ‖coordLin n y‖ ≤ C * ‖e y‖ := by
    intro n
    refine ⟨K / ‖x n‖, ?_⟩
    intro y
    let c : ℕ →₀ ℂ := h_li.repr y
    have hxpos : 0 < ‖x n‖ := norm_pos_iff.mpr (h_li.ne_zero n)
    have hK_nonneg : 0 ≤ K := by
      have hself :
          ‖∑ j ∈ ({n} : Finset ℕ), (if j = n then (1 : ℂ) else 0) • x j‖
            ≤ K * ‖∑ j ∈ ({n} : Finset ℕ), (if j = n then (1 : ℂ) else 0) • x j‖ :=
        h_proj ({n} : Finset ℕ) ({n} : Finset ℕ) (by intro j hj; simpa using hj)
          (fun j => if j = n then (1 : ℂ) else 0)
      have hself' : ‖x n‖ ≤ K * ‖x n‖ := by
        simpa using hself
      have hright_nonneg : 0 ≤ K * ‖x n‖ :=
        (norm_nonneg (x n)).trans hself'
      exact nonneg_of_mul_nonneg_right (by simpa [mul_comm] using hright_nonneg) hxpos
    by_cases hcn : c n = 0
    · simp [coordLin, c, hcn]
      exact mul_nonneg (div_nonneg hK_nonneg (norm_nonneg _)) (norm_nonneg _)
    · have hnmem : n ∈ c.support := Finsupp.mem_support_iff.mpr hcn
      have hsingleton_subset : ({n} : Finset ℕ) ⊆ c.support := by
        intro j hj
        have hji : j = n := by simpa using hj
        simpa [hji] using hnmem
      have hproj_single :
          ‖∑ j ∈ ({n} : Finset ℕ), c j • x j‖
            ≤ K * ‖∑ j ∈ c.support, c j • x j‖ :=
        h_proj c.support ({n} : Finset ℕ) hsingleton_subset (fun j => c j)
      have hsupport_sum : ∑ j ∈ c.support, c j • x j = (y : E) := by
        simpa [c, Finsupp.linearCombination_apply] using h_li.linearCombination_repr y
      have hbound : ‖c n • x n‖ ≤ K * ‖(y : E)‖ := by
        simpa [hsupport_sum] using hproj_single
      have hmul : ‖c n‖ * ‖x n‖ ≤ K * ‖(y : E)‖ := by
        simpa [norm_smul] using hbound
      calc
        ‖coordLin n y‖ = ‖c n‖ := by
          simp [coordLin, c]
        _ = (‖c n‖ * ‖x n‖) / ‖x n‖ := by
          exact (mul_div_cancel_right₀ ‖c n‖ hxpos.ne').symm
        _ ≤ (K * ‖(y : E)‖) / ‖x n‖ := by
          exact div_le_div_of_nonneg_right hmul (le_of_lt hxpos)
        _ = (K / ‖x n‖) * ‖e y‖ := by
          simp [e]
          ring
  let coeff : ℕ → E →L[ℂ] ℂ := fun n => (coordLin n).extendOfNorm e
  refine ⟨coeff, ?_⟩
  intro s a n
  let r : Finset ℕ := s
  let y : S := ⟨∑ i ∈ r, a i • x i, by
    refine Submodule.sum_mem S ?_
    intro i _hi
    exact Submodule.smul_mem S (a i) (Submodule.subset_span ⟨i, rfl⟩)⟩
  have hy : e y = ∑ i ∈ r, a i • x i := rfl
  have hcoeff_apply :
      coeff n (∑ i ∈ r, a i • x i) = coordLin n y := by
    rw [← hy]
    exact LinearMap.extendOfNorm_eq h_dense (h_norm n) y
  let ftrunc : ℕ → ℂ := fun i => if i ∈ r then a i else 0
  have hftrunc : ∀ i, ftrunc i ≠ 0 → i ∈ r := by
      intro i hi
      by_contra hir
      simp [ftrunc, hir] at hi
  let l : ℕ →₀ ℂ := Finsupp.onFinset r ftrunc hftrunc
  have hl_apply_n : l n = if n ∈ r then a n else 0 := by
    by_cases hnmem : n ∈ r <;> simp [l, ftrunc, hnmem]
  have hl_lc : Finsupp.linearCombination ℂ x l = (y : E) := by
    rw [show l = Finsupp.onFinset r ftrunc hftrunc by rfl]
    rw [Finsupp.linearCombination_onFinset]
    simp [ftrunc, y]
  have hrepr : h_li.repr y = l := h_li.repr_eq hl_lc
  calc
    coeff n (∑ i ∈ s, a i • x i)
        = coeff n (∑ i ∈ r, a i • x i) := by rfl
    _ = coordLin n y := hcoeff_apply
    _ = l n := by simp [coordLin, hrepr]
    _ = if n ∈ s then a n else 0 := by simpa [r] using hl_apply_n

/--
The continuous coordinate maps associated to the finite-projection construction.

The actual analytic construction is isolated in
`exists_coordMaps_of_finiteProjectionBound`; this definition is the chosen
coordinate family from that existence statement.
-/
noncomputable def coordMaps_of_finiteProjectionBound
    (x : ℕ → E)
    (hx_dense : HasDenseSpan x)
    (h_li : LinearIndependent ℂ x)
    (K : ℝ)
    (h_proj : FiniteProjectionBound x K) :
    ℕ → E →L[ℂ] ℂ :=
  Classical.choose
    (exists_coordMaps_of_finiteProjectionBound x hx_dense h_li K h_proj)

/--
The chosen coordinate maps agree with finite-dimensional coordinate
projections on every initial finite span.
-/
theorem coordMaps_of_finiteProjectionBound_apply_finite_sum
    (x : ℕ → E)
    (hx_dense : HasDenseSpan x)
    (h_li : LinearIndependent ℂ x)
    (K : ℝ)
    (h_proj : FiniteProjectionBound x K)
    (n k : ℕ)
    (hnk : n ≤ k)
    (a : ℕ → ℂ) :
    coordMaps_of_finiteProjectionBound x hx_dense h_li K h_proj n
      (∑ i ∈ Finset.range (k + 1), a i • x i) = a n :=
by
  have h :=
    Classical.choose_spec
      (exists_coordMaps_of_finiteProjectionBound x hx_dense h_li K h_proj)
      (Finset.range (k + 1)) a n
  simpa [Nat.lt_succ_iff, hnk] using h

/--
The finite partial-sum projections associated to the constructed coordinates
converge strongly to the identity.

This is the analytic core of the construction: the finite projection estimate
gives a uniform operator bound for all finite coordinate projections, and the
dense span hypothesis identifies the limit on a dense subspace.
-/
lemma coordMaps_tendsto_finite_partial_sums_of_finiteProjectionBound
    (x : ℕ → E)
    (hx_dense : HasDenseSpan x)
    (h_li : LinearIndependent ℂ x)
    (K : ℝ)
    (h_proj : FiniteProjectionBound x K)
    (y : E) :
    Filter.Tendsto
      (fun s : Finset ℕ =>
        ∑ n ∈ s, coordMaps_of_finiteProjectionBound x hx_dense h_li K h_proj n y • x n)
      atTop
      (𝓝 y) := by
  classical
  let coeff := coordMaps_of_finiteProjectionBound x hx_dense h_li K h_proj
  let P : Finset ℕ → E → E := fun s y => ∑ n ∈ s, coeff n y • x n
  let S : Submodule ℂ E := Submodule.span ℂ (Set.range x)
  let e : S →ₗ[ℂ] E := Submodule.subtype S
  have h_dense : DenseRange e := by
    rw [denseRange_iff_closure_range]
    simpa [HasDenseSpan, S, e, LinearMap.range_eq_map, Submodule.range_subtype] using hx_dense
  have hK_nonneg : 0 ≤ K := by
    have hself :
        ‖∑ j ∈ ({0} : Finset ℕ), (if j = 0 then (1 : ℂ) else 0) • x j‖
          ≤ K * ‖∑ j ∈ ({0} : Finset ℕ), (if j = 0 then (1 : ℂ) else 0) • x j‖ :=
      h_proj ({0} : Finset ℕ) ({0} : Finset ℕ) (by intro j hj; simpa using hj)
        (fun j => if j = 0 then (1 : ℂ) else 0)
    have hself' : ‖x 0‖ ≤ K * ‖x 0‖ := by
      simpa using hself
    have hxpos : 0 < ‖x 0‖ := norm_pos_iff.mpr (h_li.ne_zero 0)
    have hright_nonneg : 0 ≤ K * ‖x 0‖ :=
      (norm_nonneg (x 0)).trans hself'
    exact nonneg_of_mul_nonneg_right (by simpa [mul_comm] using hright_nonneg) hxpos
  have hP_span_exact :
      ∀ (s : Finset ℕ) (z : S),
        (h_li.repr z).support ⊆ s → P s (z : E) = (z : E) := by
    intro s z hzs
    let c : ℕ →₀ ℂ := h_li.repr z
    have hzsum : ∑ n ∈ c.support, c n • x n = (z : E) := by
      simpa [c, Finsupp.linearCombination_apply] using h_li.linearCombination_repr z
    have hcoord : ∀ n, coeff n (z : E) = if n ∈ c.support then c n else 0 := by
      intro n
      have h :=
        Classical.choose_spec
          (exists_coordMaps_of_finiteProjectionBound x hx_dense h_li K h_proj)
          c.support (fun i => c i) n
      simpa [coeff, hzsum] using h
    calc
      P s (z : E)
          = ∑ n ∈ s, (if n ∈ c.support then c n else 0) • x n := by
            refine Finset.sum_congr rfl ?_
            intro n _hn
            rw [hcoord n]
      _ = ∑ n ∈ s, c n • x n := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            by_cases hnc : n ∈ c.support
            · simp [hnc]
            · have hcn : c n = 0 := by simpa [Finsupp.mem_support_iff] using hnc
              simp [hnc, hcn]
      _ = ∑ n ∈ c.support, c n • x n := by
            exact (Finset.sum_subset hzs (by
              intro n _hns hnc
              have hcn : c n = 0 := by simpa [Finsupp.mem_support_iff] using hnc
              simp [hcn])).symm
      _ = (z : E) := hzsum
  have hP_span_bound :
      ∀ (s : Finset ℕ) (z : S), ‖P s (z : E)‖ ≤ K * ‖(z : E)‖ := by
    intro s z
    let c : ℕ →₀ ℂ := h_li.repr z
    have hzsum : ∑ n ∈ c.support, c n • x n = (z : E) := by
      simpa [c, Finsupp.linearCombination_apply] using h_li.linearCombination_repr z
    have hcoord : ∀ n, coeff n (z : E) = if n ∈ c.support then c n else 0 := by
      intro n
      have h :=
        Classical.choose_spec
          (exists_coordMaps_of_finiteProjectionBound x hx_dense h_li K h_proj)
          c.support (fun i => c i) n
      simpa [coeff, hzsum] using h
    have hP_eq :
        P s (z : E) = ∑ n ∈ s ∩ c.support, c n • x n := by
      calc
        P s (z : E)
            = ∑ n ∈ s, (if n ∈ c.support then c n else 0) • x n := by
              refine Finset.sum_congr rfl ?_
              intro n _hn
              rw [hcoord n]
        _ = ∑ n ∈ s ∩ c.support, (if n ∈ c.support then c n else 0) • x n := by
              exact (Finset.sum_subset (Finset.inter_subset_left) (by
                intro n _hns hninter
                have hnc : n ∉ c.support := by
                  intro hnc
                  exact hninter (Finset.mem_inter.mpr ⟨_hns, hnc⟩)
                simp [hnc])).symm
        _ = ∑ n ∈ s ∩ c.support, c n • x n := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              have hnc : n ∈ c.support := (Finset.mem_inter.mp hn).2
              simp [hnc]
    have hproj_bound :
        ‖∑ n ∈ s ∩ c.support, c n • x n‖
          ≤ K * ‖∑ n ∈ c.support, c n • x n‖ :=
      h_proj c.support (s ∩ c.support) (Finset.inter_subset_right) (fun n => c n)
    simpa [hP_eq, hzsum]
      using hproj_bound
  have hP_bound :
      ∀ (s : Finset ℕ) (y : E), ‖P s y‖ ≤ K * ‖y‖ := by
    intro s y
    exact h_dense.induction_on y
      (isClosed_le (by fun_prop) (by fun_prop))
      (fun z => by simpa [e] using hP_span_bound s z)
  rw [NormedAddCommGroup.tendsto_atTop]
  intro ε hε
  have hK1_pos : 0 < K + 1 := by linarith
  let δ : ℝ := ε / (K + 1)
  have hδ_pos : 0 < δ := div_pos hε hK1_pos
  obtain ⟨z, hzdist⟩ := h_dense.exists_dist_lt y hδ_pos
  let c : ℕ →₀ ℂ := h_li.repr z
  refine ⟨c.support, ?_⟩
  intro s hs
  have hPz : P s (z : E) = (z : E) :=
    hP_span_exact s z (by simpa [c] using hs)
  have hP_sub :
      P s (y - (z : E)) = P s y - P s (z : E) := by
    simp [P, map_sub, sub_smul, Finset.sum_sub_distrib]
  have hdecomp :
      P s y - y = P s (y - (z : E)) + ((z : E) - y) := by
    rw [hP_sub, hPz]
    abel
  have hynorm_lt : ‖y - (z : E)‖ < δ := by
    simpa [dist_eq_norm] using hzdist
  calc
    ‖P s y - y‖ = ‖P s (y - (z : E)) + ((z : E) - y)‖ := by rw [hdecomp]
    _ ≤ ‖P s (y - (z : E))‖ + ‖(z : E) - y‖ := norm_add_le _ _
    _ ≤ K * ‖y - (z : E)‖ + ‖(z : E) - y‖ := by
          exact add_le_add (hP_bound s (y - (z : E))) le_rfl
    _ = (K + 1) * ‖y - (z : E)‖ := by
          rw [norm_sub_rev]
          ring
    _ < (K + 1) * δ := mul_lt_mul_of_pos_left hynorm_lt hK1_pos
    _ = ε := by
          dsimp [δ]
          field_simp [hK1_pos.ne']

/-- The extended coordinate maps reconstruct every vector as a Schauder sum. -/
lemma coordMaps_hasSum_repr_of_finiteProjectionBound
    (x : ℕ → E)
    (hx_dense : HasDenseSpan x)
    (h_li : LinearIndependent ℂ x)
    (K : ℝ)
    (h_proj : FiniteProjectionBound x K)
    (y : E) :
    HasSum
      (fun n : ℕ =>
        coordMaps_of_finiteProjectionBound x hx_dense h_li K h_proj n y • x n)
      y := by
  simpa [HasSum, SummationFilter.unconditional_filter] using
    coordMaps_tendsto_finite_partial_sums_of_finiteProjectionBound x hx_dense h_li K h_proj y

/-- Coefficients in the resulting expansion are unique. -/
lemma coordMaps_unique_of_finiteProjectionBound
    (x : ℕ → E)
    (hx_dense : HasDenseSpan x)
    (h_li : LinearIndependent ℂ x)
    (K : ℝ)
    (h_proj : FiniteProjectionBound x K) :
    ∀ (y : E) (a : ℕ → ℂ),
      HasSum (fun n : ℕ => a n • x n) y →
        a = fun n : ℕ =>
          coordMaps_of_finiteProjectionBound x hx_dense h_li K h_proj n y := by
  classical
  intro y a ha
  funext n
  let coeff := coordMaps_of_finiteProjectionBound x hx_dense h_li K h_proj
  have hmap : HasSum (fun m : ℕ => coeff n (a m • x m)) (coeff n y) :=
    ha.mapL (coeff n)
  have hpartial :
      ∀ᶠ s : Finset ℕ in atTop,
        (∑ m ∈ s, coeff n (a m • x m)) = a n := by
    filter_upwards [eventually_ge_atTop ({n} : Finset ℕ)] with s hs
    have hns : n ∈ s := hs (by simp)
    have hcoord :=
      Classical.choose_spec
        (exists_coordMaps_of_finiteProjectionBound x hx_dense h_li K h_proj)
        s a n
    calc
      (∑ m ∈ s, coeff n (a m • x m))
          = coeff n (∑ m ∈ s, a m • x m) := by
            exact (map_sum (coeff n) (fun m => a m • x m) s).symm
      _ = a n := by
            simpa [coeff, hns] using hcoord
  have hscalar : HasSum (fun m : ℕ => coeff n (a m • x m)) (a n) := by
    rw [HasSum, SummationFilter.unconditional_filter]
    exact (tendsto_congr' hpartial).mpr tendsto_const_nhds
  exact HasSum.unique hscalar hmap

/-- The coordinate expansions are unconditional. -/
lemma coordMaps_unconditional_of_finiteProjectionBound
    (x : ℕ → E)
    (hx_dense : HasDenseSpan x)
    (h_li : LinearIndependent ℂ x)
    (K : ℝ)
    (h_proj : FiniteProjectionBound x K) :
    ∀ (y : E) (σ : Equiv.Perm ℕ),
      HasSum
        (fun n : ℕ =>
          coordMaps_of_finiteProjectionBound x hx_dense h_li K h_proj (σ n) y • x (σ n))
        y := by
  intro y σ
  let f : ℕ → E :=
    fun n => coordMaps_of_finiteProjectionBound x hx_dense h_li K h_proj n y • x n
  have hf : HasSum f y :=
    coordMaps_hasSum_repr_of_finiteProjectionBound x hx_dense h_li K h_proj y
  simpa [f, Function.comp_def] using (σ.hasSum_iff).2 hf

/-- Package the constructed coordinates and convergence facts as `SchauderData`. -/
noncomputable def schauderData_of_finiteProjectionBound
    (x : ℕ → E)
    (hx_dense : HasDenseSpan x)
    (h_li : LinearIndependent ℂ x)
    (K : ℝ)
    (h_proj : FiniteProjectionBound x K) :
    SchauderData E :=
{
  basis := x
  coeff := coordMaps_of_finiteProjectionBound x hx_dense h_li K h_proj
  hasSum_repr :=
    coordMaps_hasSum_repr_of_finiteProjectionBound x hx_dense h_li K h_proj
  unique_coeff :=
    coordMaps_unique_of_finiteProjectionBound x hx_dense h_li K h_proj
  unconditional :=
    coordMaps_unconditional_of_finiteProjectionBound x hx_dense h_li K h_proj
}

/--
A dense sequence satisfying the finite signed unconditionality estimate should
produce an unconditional Schauder basis.

This is the final criterion in the notation of this file. The proof is left
as the main construction task: one has to build the continuous coordinate
functionals from the uniformly bounded finite projections, extend them from the
algebraic span to all of `E`, and then prove convergence and uniqueness.
-/
noncomputable def unconditionalSchauderBasis_of_finiteSignBound
    (x : ℕ → E)
    (hx_dense : HasDenseSpan x)
    (hx_ne : ∀ n, x n ≠ 0)
    (C : ℝ)
    (hC : 0 ≤ C)
    (h_sign : HasFiniteSignBound x C) :
    UnconditionalSchauderBasis E := by
  let K : ℝ := (C + 1) / 2
  have h_proj : FiniteProjectionBound x K :=
    finiteProjectionBound_of_signBound x C hC h_sign
  have h_li : LinearIndependent ℂ x :=
    linearIndependent_of_finiteProjectionBound x hx_ne K h_proj
  exact
    (schauderData_of_finiteProjectionBound x hx_dense h_li K h_proj).toUnconditionalSchauderBasis

/--
The finite signed estimate, dense span, and non-vanishing of the vectors imply
that `x` is the basis sequence of some unconditional Schauder basis.
-/
theorem exists_unconditionalSchauderBasis_of_finiteSignBound
    (x : ℕ → E)
    (hx_dense : HasDenseSpan x)
    (hx_ne : ∀ n, x n ≠ 0)
    (C : ℝ)
    (hC : 0 ≤ C)
    (h_sign : HasFiniteSignBound x C) :
    ∃ b : UnconditionalSchauderBasis E, b.basis = x := by
  refine ⟨unconditionalSchauderBasis_of_finiteSignBound x hx_dense hx_ne C hC h_sign, ?_⟩
  rfl

end UnconditionalCriterion
