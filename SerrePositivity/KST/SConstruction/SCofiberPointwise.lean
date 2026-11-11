module
public import SerrePositivity.KST.SConstruction.SCofiberTranspose
public import SerrePositivity.KST.SConstruction.FullSubcomplexUniversalVertices

/-! # S_n 内の cofiber 四角形の点ごとの判定
概要：S_n の四角形が cofiber である条件を、Ar[n] の全頂点で判定する。
方針：関手圏の零対象の点ごとの判定と gapped 包含の cofiber 判定を合わせる。
規約：零角は仮定せず各点から回収する。使われ方：cofiber 図式の交換の両方向。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- S_n の頂点は、その全 Ar 成分が零なら零対象。 -/
lemma gappedVertex_isZero_of_pointwise {n : ℕ} {C : SSet.{u}}
    (v : (sConstruction n C) _⦋0⦌)
    (hv : ∀ a : (arNerve n) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) a).app (Opposite.op ⦋0⦌) v.val)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex v := by
  have hz := isZeroVertex_of_pointwise v.val hv
  exact ⟨isInitialVertex_fullSubcomplex_of_ambient _ _ hz.1,
    isTerminalVertex_fullSubcomplex_of_ambient _ _ hz.2⟩

/-- S_n の零角と押し出し性は全 Ar 成分での cofiber 条件と同値。 -/
lemma gappedSquare_cofiber_iff_pointwise {n : ℕ} {C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (G : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ sConstruction n C) :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex G 0 1) ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare G) ↔
      ∀ a : (arNerve n) _⦋0⦌,
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (G ≫ (gappedSubcomplex n C).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a) 0 1) ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (G ≫ (gappedSubcomplex n C).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a) := by
  constructor
  · rintro ⟨hz, hG⟩ a
    have he := (gappedInclusion_preservesSConstructionData n C).comp
      (evaluateFunctorAt_preservesSConstructionData a)
    exact ⟨he.1 _ hz, he.2 G hG⟩
  · intro h
    have hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex G 0 1) :=
      gappedVertex_isZero_of_pointwise _ (fun a => (h a).1)
    refine ⟨hz, ?_⟩
    exact (gappedInclusion_cofiber_iff_pointwise (⟨G, hz⟩ : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle (sConstruction n C))).2
      (fun a => (h a).2)

end SerrePositivity.KST.SConstruction
