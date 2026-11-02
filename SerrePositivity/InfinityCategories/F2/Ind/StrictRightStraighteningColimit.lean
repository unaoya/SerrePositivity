module

public import SerrePositivity.InfinityCategories.F2.Ind.StrictOppositeFiberColimit
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafPointwiseColimits
public import SerrePositivity.InfinityCategories.F1.SquareFunctorTransport

/-!
概要：strict filtered right fibration 余極限の同じ分類余錐は前層 ∞ 圏の余極限。
方針：同じ余錐の全評価を元の反転 fiber 余錐へ比較し、既存の点ごとの検出を適用する。
規約：全脚と全高次の整合性を持つ元の指定余錐の普遍性。
使われ方：Indκ の元の圏の閉性を coherent な前層余極限へ接続する strict 模型側の定理。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable {B : SSet.{u}} {I : Type u} [SmallCategory I] [IsFiltered I]

/-- 同じ元の前層余錐の各評価は SpaceInfinity の native な余極限。 -/
lemma strictRightStraighteningCocone_evaluation_isColimit
    (F : I ⥤ RightFibrationObject B) (b : B _⦋0⦌) :
    IsColimitCone (mapJoinCocone (presheafInfinityEvaluation b)
      (strictRightStraighteningCocone F)) := by
  apply IsColimitCone.of_functorIso (strictOppositeFiberNativeCocone_isColimit F b)
  exact (strictRightStraighteningColimitFiberCoconeIso F (SSet.opObjEquiv.symm b)).symm

/-- 元の strict filtered 余極限の同じ right straightening 余錐は前層 ∞ 圏の余極限。 -/
lemma strictRightStraighteningCocone_isColimit [Quasicategory B]
    (F : I ⥤ RightFibrationObject B) : IsColimitCone (strictRightStraighteningCocone F) :=
  presheafInfinity_isColimit_of_evaluation _ _
    (strictRightStraighteningCocone_evaluation_isColimit F)

end SerrePositivity.InfinityCategories.F2.Ind
