module
public import SerrePositivity.KST.SConstruction.CutDoubleCofiberVanishing
public import SerrePositivity.KST.SConstruction.TrivialFibrationFunctorIsoReflection

/-! # 相対切断と中央評価の実際の同値
概要：左右支持の相対 E と S_n C を切断比較・中央評価で同値にする。
方針：二重 cofiber 格子から元の下辺の族を同型にし、射影と包含を通して反映する。
規約：厳密な切断と coherent な逆同型を使う。使われ方：相対加法性から Segal 射へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

/-- 相対切断の中央評価後の切断と元の相対 cofiber の入力族は coherent に同型。 -/
def cutRelativeInputIso (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((cutRelativeMiddle n k X ≫ cutStableComparison n k X).val ≫
        cofiberProjection (sConstruction n X.carrier))
      ((relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X)).val ≫
        cofiberProjection (sConstruction n X.carrier)) := by
  have h := doubleCofiberInputIso (cutDoubleCofiberFamily n k X)
    (cutDoubleCofiberFamily_row_zero_isZero n k X)
    (cutDoubleCofiberFamily_column_zero_isZero n k X)
  rw [cutDoubleCofiberFamily_row_one, cutDoubleCofiberFamily_column_one] at h
  exact h

/-- 中央評価の後の切断と元の cofiber 族は全ての選択を保った関手同型。 -/
def cutRelativeAmbientIso (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cutRelativeMiddle n k X ≫ cutStableComparison n k X).val
      (relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X)).val :=
  functorIsoOfTrivialKanFibrationPostcomp (cofiberProjection (sConstruction n X.carrier))
    (cutRelativeInputIso n k X)

/-- 中央評価の後の相対切断比較は相対 E の内部で恒等関手と coherent に同型。 -/
def cutRelativeMiddle_comparisonIso (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cutRelativeMiddle n k X ≫ cutRelativeComparison n k X).val
      (𝟙 (relativeCofiberDiagrams (cutLeftSupport n k X) (cutRightSupport n k X))) := by
  apply functorIsoOfFullSubcomplexPostcomp
    (relativeCofiberPredicate (cutLeftSupport n k X) (cutRightSupport n k X)).predicate
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (((cutRelativeMiddle n k X ≫ cutRelativeComparison n k X) ≫
      relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X)).val)
    (𝟙 _ ≫ (relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X)).val)
  rw [Category.id_comp]
  have h : (cutRelativeMiddle n k X ≫ cutRelativeComparison n k X) ≫
      relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X) =
    cutRelativeMiddle n k X ≫ cutStableComparison n k X :=
    (Category.assoc _ _ _).trans
      (congrArg (fun f => cutRelativeMiddle n k X ≫ f) (cutRelativeComparison_inclusion n k X))
  rw [congrArg Subtype.val h]
  exact cutRelativeAmbientIso n k X

/-- 任意の切断位置の左右支持の相対 E と S_n C の実際の quasicategory 同値。 -/
def cutRelativeEquivalence (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (sConstruction n X.carrier)
      (relativeCofiberDiagrams (cutLeftSupport n k X) (cutRightSupport n k X)) where
  hom := (cutRelativeComparison n k X).val
  inv := (cutRelativeMiddle n k X).val
  homInvIso := eqToIso (congrArg (fun f => SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
    (congrArg Subtype.val (cutRelativeComparison_middle n k X)))
  invHomIso := cutRelativeMiddle_comparisonIso n k X

end SerrePositivity.KST.SConstruction
