module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonGradedProjection
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # 長さ filtration の随伴次数部分と固定長 path 直和 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
attribute [local instance] Classical.propDecidable

/-- 内部微分の直和上で、長さ n 以下だけを残す射影。 -/
def lengthCutoff (S : Set D) (x y : D) (n : ℕ) : internalHom A D S x y ⟶ internalHom A D S x y :=
  selectedProjection A D S (fun w => w.length ≤ n) x y ≫
    selectedInclusion A D S (fun w => w.length ≤ n) x y

lemma ι_lengthCutoff (S : Set D) (x y : D) (n : ℕ) (w : Word S) :
    ι A D S x y w ≫ lengthCutoff A D S x y n =
      if w.length ≤ n then ι A D S x y w else 0 := by
  rw [lengthCutoff, ← Category.assoc, ι_selectedProjection]
  by_cases h : w.length ≤ n
  · rw [dite_eq_left h, ite_eq_left h, selected_ι_inclusion]
  · rw [dite_eq_right h, ite_eq_right h, zero_comp]

lemma lengthCutoff_mem (S : Set D) (x y : D) (n : ℕ) (i : ℤ)
    (z : (internalHom A D S x y).X i) :
    (lengthCutoff A D S x y n).f i z ∈ lengthSubmodule A D S x y n i :=
  selectedInclusion_mem_length A D S (fun w => w.length ≤ n) x y n (fun _ h => h) i _

lemma lengthCutoff_fixed (S : Set D) (x y : D) (n : ℕ) (i : ℤ)
    (z : (internalHom A D S x y).X i) (hz : z ∈ lengthSubmodule A D S x y n i) :
    (lengthCutoff A D S x y n).f i z = z := by
  have hle : lengthSubmodule A D S x y n i ≤
      LinearMap.ker (((lengthCutoff A D S x y n).f i).hom - LinearMap.id) := by
    refine iSup_le (fun w => iSup_le (fun hw => ?_))
    rintro t ⟨v, rfl⟩
    have h := congrArg (fun f => f.f i v) (ι_lengthCutoff A D S x y n w)
    simp only [ite_eq_left hw, HomologicalComplex.comp_f, ModuleCat.comp_apply] at h
    exact sub_eq_zero.mpr h
  exact sub_eq_zero.mp (hle hz)

lemma ι_fixedLengthProjector (S : Set D) (x y : D) (n : ℕ) (w : Word S) :
    ι A D S x y w ≫
        (fixedLengthProjection A D S x y n ≫ fixedLengthInclusion A D S x y n) =
      if w.length = n then ι A D S x y w else 0 := by
  rw [← Category.assoc, ι_selectedProjection]
  by_cases h : w.length = n
  · rw [dite_eq_left h, ite_eq_left h, selected_ι_inclusion]
  · rw [dite_eq_right h, ite_eq_right h, zero_comp]

/-- 相隣る cutoff の差は、その固定長成分への射影である。 -/
lemma lengthCutoff_succ (S : Set D) (x y : D) (n : ℕ) :
    lengthCutoff A D S x y (n + 1) = lengthCutoff A D S x y n +
      fixedLengthProjection A D S x y (n + 1) ≫ fixedLengthInclusion A D S x y (n + 1) := by
  apply Sigma.hom_ext
  intro w
  change ι A D S x y w ≫ lengthCutoff A D S x y (n + 1) =
    ι A D S x y w ≫ (lengthCutoff A D S x y n +
      fixedLengthProjection A D S x y (n + 1) ≫ fixedLengthInclusion A D S x y (n + 1))
  rw [Preadditive.comp_add, ι_lengthCutoff, ι_lengthCutoff, ι_fixedLengthProjector]
  by_cases h : w.length ≤ n
  · have hn : w.length ≤ n + 1 := by omega
    have he : w.length ≠ n + 1 := by omega
    rw [ite_eq_left hn, ite_eq_left h, ite_eq_right he, add_zero]
  · by_cases he : w.length = n + 1
    · have hn : w.length ≤ n + 1 := by omega
      rw [ite_eq_left hn, ite_eq_right h, ite_eq_left he, zero_add]
    · have hn : ¬ w.length ≤ n + 1 := by omega
      rw [ite_eq_right hn, ite_eq_right h, ite_eq_right he, add_zero]

/-- 固定長射影の核は、ちょうど一段前の filtration である。 -/
lemma lengthLayerProjection_kernel (S : Set D) (x y : D) (n : ℕ) (i : ℤ)
    (z : lengthSubmodule A D S x y (n + 1) i) :
    (lengthLayerProjection A D S x y n).f i z = 0 ↔
      z.val ∈ lengthSubmodule A D S x y n i := by
  constructor
  · intro hz
    have hp : (fixedLengthProjection A D S x y (n + 1)).f i z.val = 0 := hz
    have h := congrArg (fun f => f.f i z.val) (lengthCutoff_succ A D S x y n)
    change (lengthCutoff A D S x y (n + 1)).f i z.val =
      (lengthCutoff A D S x y n).f i z.val +
        (fixedLengthInclusion A D S x y (n + 1)).f i
          ((fixedLengthProjection A D S x y (n + 1)).f i z.val) at h
    rw [hp, map_zero, add_zero] at h
    rw [lengthCutoff_fixed A D S x y (n + 1) i z.val z.property] at h
    rw [h]
    exact lengthCutoff_mem A D S x y n i z.val
  · intro hz
    exact fixedLengthProjection_kills_lower A D S x y n i hz

lemma lengthLayerProjection_surjective (S : Set D) (x y : D) (n : ℕ) (i : ℤ) :
    Function.Surjective ((lengthLayerProjection A D S x y n).f i) := by
  intro z
  let t : lengthSubmodule A D S x y (n + 1) i :=
    ⟨(fixedLengthInclusion A D S x y (n + 1)).f i z,
      selectedInclusion_mem_length A D S (fun w => w.length = n + 1) x y (n + 1)
        (fun _ h => h.le) i z⟩
  refine ⟨t, ?_⟩
  have h := congrArg (fun f => f.f i z)
    (selectedInclusion_projection A D S (fun w => w.length = n + 1) x y)
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, HomologicalComplex.id_f,
    ModuleCat.id_apply] at h
  convert h using 1
  rfl

private lemma inclusion_exact_of_kernel {V W : Type*}
    [AddCommGroup V] [AddCommGroup W] [Module A V] [Module A W]
    (P Q : Submodule A V) (hPQ : P ≤ Q) (g : Q →ₗ[A] W)
    (h : ∀ z : Q, g z = 0 ↔ z.val ∈ P) : Function.Exact (Submodule.inclusion hPQ) g := by
  intro z
  rw [h]
  constructor
  · intro hz
    exact ⟨⟨z.val, hz⟩, Subtype.ext rfl⟩
  · rintro ⟨t, rfl⟩
    exact t.property

lemma lengthLayerProjection_exact (S : Set D) (x y : D) (n : ℕ) (i : ℤ) :
    Function.Exact ((lengthMap A D S x y (Nat.le_succ n)).f i).hom
      ((lengthLayerProjection A D S x y n).f i).hom := by
  exact inclusion_exact_of_kernel A _ _
    (lengthSubmodule_mono A D S x y (Nat.le_succ n) i) _
    (lengthLayerProjection_kernel A D S x y n i)

lemma lengthMap_layerProjection (S : Set D) (x y : D) (n : ℕ) :
    lengthMap A D S x y (Nat.le_succ n) ≫ lengthLayerProjection A D S x y n = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact ModuleCat.hom_ext (lengthLayerProjection_exact A D S x y n i).linearMap_comp_eq_zero

/-- 固定長直和を第三項とする実際の短複体。 -/
def lengthLayerShortComplex (S : Set D) (x y : D) (n : ℕ) : ShortComplex (Complex A) :=
  ShortComplex.mk (lengthMap A D S x y (Nat.le_succ n)) (lengthLayerProjection A D S x y n)
    (lengthMap_layerProjection A D S x y n)

/-- 各次数で固定長 path への射影は、前段階の包含の cokernel である。 -/
def lengthLayer_eval_isColimit (S : Set D) (x y : D) (n : ℕ) (i : ℤ) :
    IsColimit (CokernelCofork.ofπ ((lengthLayerProjection A D S x y n).f i)
      (show (lengthMap A D S x y (Nat.le_succ n)).f i ≫
          (lengthLayerProjection A D S x y n).f i = 0 from
        congrArg (fun f => f.f i) (lengthMap_layerProjection A D S x y n))) :=
  ModuleCat.isColimitCokernelCofork _ _ (lengthLayerProjection_exact A D S x y n i)
    (lengthLayerProjection_surjective A D S x y n i)

/-- 複体としても、固定長直和は相隣る長さ部分複体の cokernel。 -/
def lengthLayer_isColimit (S : Set D) (x y : D) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (lengthLayerProjection A D S x y n)
      (lengthMap_layerProjection A D S x y n)) := by
  apply HomologicalComplex.isColimitOfEval
  intro i
  exact (isColimitMapCoconeCoforkEquiv'
    (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)
    (lengthMap_layerProjection A D S x y n)).symm (lengthLayer_eval_isColimit A D S x y n i)

/-- 正の随伴次数部分の、内部微分を持つ固定長 path 直和としての計算。 -/
def lengthGradedIso (S : Set D) (x y : D) (n : ℕ) :
    cokernel (lengthMap A D S x y (Nat.le_succ n)) ≅ fixedLengthHom A D S x y (n + 1) :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso (lengthLayer_isColimit A D S x y n)

/-- 相隣る filtration と固定長直和は、複体の短完全列をなす。 -/
lemma lengthLayer_shortExact (S : Set D) (x y : D) (n : ℕ) :
    (lengthLayerShortComplex A D S x y n).ShortExact := by
  have hm : Mono (lengthMap A D S x y (Nat.le_succ n)) :=
    mono_of_mono_fac (lengthMap_inclusion A D S x y (Nat.le_succ n))
  have hc := lengthLayer_isColimit A D S x y n
  exact
    { exact := (lengthLayerShortComplex A D S x y n).exact_of_g_is_cokernel hc
      mono_f := hm
      epi_g := epi_of_isColimit_cofork hc }

@[reassoc] lemma lengthGradedIso_π (S : Set D) (x y : D) (n : ℕ) :
    cokernel.π (lengthMap A D S x y (Nat.le_succ n)) ≫ (lengthGradedIso A D S x y n).hom =
      lengthLayerProjection A D S x y n :=
  (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom _ WalkingParallelPair.one

end SerrePositivity.DifferentialGraded.DGQuotient
