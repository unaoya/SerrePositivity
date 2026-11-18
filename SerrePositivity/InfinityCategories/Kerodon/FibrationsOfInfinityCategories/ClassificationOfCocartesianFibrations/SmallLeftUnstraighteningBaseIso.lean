module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningBaseChange

/-!
概要：小さい unstraightening の既存の底変換射を、底の同型に対する同型として読む。
方針：既存の引き戻し四角形と同型の引き戻し保存を使う。
規約：比較射そのものを変えず、その射影の等式を保持する。
使われ方：Kerodon Remark 5.6.2.18（Tag 0271）、S8 の反対 nerve の形状移送。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 底の同型による既存の unstraightening の比較射は同型。
Kerodon Remark 5.6.2.18（Tag 0271）、既存の引き戻しの法則。 -/
def smallLeftUnstraighteningBaseIso {B D : SSet.{u}} (e : B ≅ D)
    (G : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ SpaceInfinity.{u}) :
    smallLeftUnstraightening ((SSet.uliftFunctor.{u + 1, u}).map e.hom ≫ G) ≅
      smallLeftUnstraightening G := by
  let f := smallLeftUnstraighteningMap
    ((SSet.uliftFunctor.{u + 1, u}).map e.hom ≫ G) G e.hom rfl
  haveI : IsIso f := (smallLeftUnstraighteningMap_isPullback
    ((SSet.uliftFunctor.{u + 1, u}).map e.hom ≫ G) G e.hom rfl).isIso_fst_of_isIso
  exact asIso f

/-- 同じ底変換の同型は、元の小さい底の同型に沿って射影を保つ。
Kerodon Remark 5.6.2.18（Tag 0271）、既存の比較射の射影の法則。 -/
lemma smallLeftUnstraighteningBaseIso_projection {B D : SSet.{u}} (e : B ≅ D)
    (G : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ SpaceInfinity.{u}) :
    (smallLeftUnstraighteningBaseIso e G).hom ≫ smallLeftUnstraighteningProjection G =
      smallLeftUnstraighteningProjection ((SSet.uliftFunctor.{u + 1, u}).map e.hom ≫ G) ≫ e.hom :=
  smallLeftUnstraighteningMap_projection _ G e.hom rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
