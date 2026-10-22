module

public import SerrePositivity.InfinityCategories.F2.Ind.PresheafDiagramJointValue
public import SerrePositivity.InfinityCategories.F1.SmallLeftUnstraighteningFunctorIso

/-!
概要：strict 化の同じ評価射を、元の前層値の元の小さい unstraightening へ戻す。
方針：under 切断の評価と、同じ共同 unstraightening の底変換同型を合成して反転する。
規約：元の値の全空間と底を保つ。大域の自然変換は別工程。
使われ方：元の前層図式と strict right fibration 図式の比較の指定成分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] {C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ PresheafInfinity C)

/-- 元の前層値の小さい left unstraightening への、指定した評価成分。 -/
def presheafDiagramLeftValueRecovery (i : I) :
    underSectionFamily (presheafDiagramJointProjection F) i ⟶
      smallLeftUnstraightening (presheafDiagramValue F i) :=
  underSectionEvaluate (presheafDiagramJointProjection F) i ≫
    (presheafDiagramJointValueIso F i).inv

/-- 同じ復元成分は元の反対底を厳密に保つ。 -/
lemma presheafDiagramLeftValueRecovery_projection (i : I) :
    presheafDiagramLeftValueRecovery F i ≫
      smallLeftUnstraighteningProjection (presheafDiagramValue F i) =
        underSectionFamilyProjection (presheafDiagramJointProjection F) i := by
  rw [presheafDiagramLeftValueRecovery, Category.assoc,
    presheafDiagramJointValueIso_inv_projection, underSectionEvaluate_projection]

/-- 元の前層値の同じ小さい right unstraightening への復元成分。 -/
def presheafDiagramRightValueRecovery (i : I) :
    ((presheafDiagramRightStrict F).obj i).val.left ⟶
      smallRightUnstraightening (presheafDiagramValue F i) :=
  SSet.opFunctor.map (presheafDiagramLeftValueRecovery F i)

/-- 同じ right 復元成分は元の底 C を厳密に保つ。 -/
lemma presheafDiagramRightValueRecovery_projection (i : I) :
    presheafDiagramRightValueRecovery F i ≫
      smallRightUnstraighteningProjection (presheafDiagramValue F i) =
        ((presheafDiagramRightStrict F).obj i).val.hom := by
  change SSet.opFunctor.map _ ≫ (SSet.opFunctor.map _ ≫ _) = _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    presheafDiagramLeftValueRecovery_projection]
  rfl

instance presheafDiagramRightValue_quasicategory [Quasicategory C] (i : I) :
    Quasicategory (smallRightUnstraightening (presheafDiagramValue F i)) :=
  inferInstanceAs (Quasicategory (smallLeftUnstraightening (presheafDiagramValue F i)).op)

/-- 元の同じ値への復元射自体の同値性。 -/
lemma presheafDiagramRightValueRecovery_isQCatEquivalence [Quasicategory C] (i : I) :
    IsQCatEquivalence (presheafDiagramRightValueRecovery F i) := by
  have h := (underSectionEvaluate_isQCatEquivalence
    (presheafDiagramJointProjection F) i).comp
      (qCatEquivalenceOfIso (presheafDiagramJointValueIso F i).symm).isQCatEquivalence
  exact h.opposite

end SerrePositivity.InfinityCategories.F2.Ind
