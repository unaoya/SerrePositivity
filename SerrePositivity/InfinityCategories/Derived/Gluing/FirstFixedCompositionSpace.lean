module
public import SerrePositivity.InfinityCategories.Derived.Gluing.FirstFixedCompositionHorn
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.CompositionCorrespondence

/-! 第一辺固定の全合成三角形の空間と、元の第二辺への自明 Kan 射影。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra SSet.modelCategoryQuillen
open scoped Simplicial
variable {X : SSet.{u}} {x y : X _⦋0⦌} (f : X.Edge x y) (z : X _⦋0⦌)

def dgGluingFirstFixedCompositionSpace : SSet.{u} :=
  pullback ((pre (horn 2 1).ι).app X) (dgGluingFirstFixedCompositionHornMap f z)

def dgGluingFirstFixedCompositionSecond :
    dgGluingFirstFixedCompositionSpace f z ⟶ intervalMappingSpace y z :=
  pullback.snd _ _

def dgGluingFirstFixedCompositionEvaluation :
    (Δ[2] : SSet.{u}) ⊗ dgGluingFirstFixedCompositionSpace f z ⟶ X :=
  uncurry (pullback.fst ((pre (horn 2 1).ι).app X)
    (dgGluingFirstFixedCompositionHornMap f z))

lemma dgGluingFirstFixedCompositionSecond_trivialKanFibration [Quasicategory X] :
    TrivialKanFibration (dgGluingFirstFixedCompositionSecond f z) := by
  let : TrivialKanFibration ((pre (horn 2 1).ι).app X) :=
    trivialKanFibration_pre_of_innerAnodyne _
      (innerAnodyneExtensions.horn_ι (by decide) (by decide)) X
  exact trivialKanFibration_pullback_snd _ _

lemma dgGluingFirstFixedCompositionSpace_kanComplex [Quasicategory X] :
    KanComplex (dgGluingFirstFixedCompositionSpace f z) := by
  let := dgGluingFirstFixedCompositionSecond_trivialKanFibration f z
  let : Fibration (dgGluingFirstFixedCompositionSecond f z) :=
    (SSet.modelCategoryQuillen.fibration_iff _).2 (by
      intro A B i hi
      exact TrivialKanFibration.mem (p := dgGluingFirstFixedCompositionSecond f z) i
        (J_le_monomorphisms i hi))
  exact isFibrant_of_fibration (dgGluingFirstFixedCompositionSecond f z)

attribute [local instance] dgGluingFirstFixedCompositionSpace_kanComplex

lemma dgGluingFirstFixedCompositionSecond_equivalence [Quasicategory X] :
    IsQCatEquivalence (dgGluingFirstFixedCompositionSecond f z) := by
  let := dgGluingFirstFixedCompositionSecond_trivialKanFibration f z
  exact isQCatEquivalence_of_trivialKanFibration _

lemma dgGluingFirstFixedCompositionEvaluation_horn :
    ((horn 2 1).ι ▷ dgGluingFirstFixedCompositionSpace f z) ≫
        dgGluingFirstFixedCompositionEvaluation f z =
      uncurry (dgGluingFirstFixedCompositionSecond f z ≫
        dgGluingFirstFixedCompositionHornMap f z) := by
  unfold dgGluingFirstFixedCompositionEvaluation dgGluingFirstFixedCompositionSecond
  rw [← uncurry_pre_app, pullback.condition]

end SerrePositivity.InfinityCategories
