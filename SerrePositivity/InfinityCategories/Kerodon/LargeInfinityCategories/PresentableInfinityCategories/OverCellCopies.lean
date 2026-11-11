module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteOverPresentable
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
概要：底上の全射で添字付けたセルのコピーと、その filtered 余極限保存。
方針：底上の Hom と copower の随伴を合成し、点ごとの余極限へ保存性を移す。
規約：底を固定した実際の関手と自然変換を構成する。
使われ方：連続な left fibration 置換の左ホーン付加。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 底上の A からの全射を添字とする D のコピー。 -/
def overCellCopiesFunctor {B : SSet.{u}} (A D : Over B) : Over B ⥤ Over B :=
  coyoneda.obj (Opposite.op A) ⋙ sigmaConst.obj D

/-- 有限な全空間を持つ始域で添字付けたコピーは filtered 余極限を保つ。 -/
instance overCellCopiesFunctor_preservesFilteredColimits {B : SSet.{u}} (A D : Over B)
    [A.left.Finite] : PreservesFilteredColimitsOfSize.{u, u} (overCellCopiesFunctor A D) := by
  have : IsFinitelyPresentable.{u} A := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteOverPresentable.finiteOver_isFinitelyPresentable A.hom
    exact h
  have := (sigmaConstAdj D).leftAdjoint_preservesColimits
  dsimp only [overCellCopiesFunctor]
  infer_instance

/-- コピーを元の添字の底上の射で評価する。 -/
def overCellCopiesEvaluation {B : SSet.{u}} (A : Over B) :
    overCellCopiesFunctor A A ⟶ 𝟭 (Over B) := (sigmaConstAdj A).counit

/-- セルの形状の射から、同じ底上の添字を保つコピーの射を作る。 -/
def overCellCopiesMap {B : SSet.{u}} (A : Over B) {D E : Over B} (i : D ⟶ E) :
    overCellCopiesFunctor A D ⟶ overCellCopiesFunctor A E :=
  Functor.whiskerLeft (coyoneda.obj (Opposite.op A)) (sigmaConst.map i)

/-- 評価の各コピーへの制限は元の底上の射である。 -/
lemma overCellCopiesEvaluation_ι {B : SSet.{u}} {A X : Over B} (t : A ⟶ X) :
    Sigma.ι (fun _ : A ⟶ X ↦ A) t ≫ (overCellCopiesEvaluation A).app X = t := by
  exact Sigma.ι_comp_desc _ _

/-- コピー間の射の各制限は、元のセルの射である。 -/
lemma overCellCopiesMap_ι {B : SSet.{u}} {A D E X : Over B} (i : D ⟶ E) (t : A ⟶ X) :
    Sigma.ι (fun _ : A ⟶ X ↦ D) t ≫ (overCellCopiesMap A i).app X =
      i ≫ Sigma.ι (fun _ : A ⟶ X ↦ E) t := by
  exact Sigma.ι_map (fun _ : A ⟶ X ↦ i) t

/-- 小さい底上の関手の点ごとの余極限は filtered 余極限保存を保つ。 -/
lemma over_preservesFilteredColimits_colimit_of_pointwise {B : SSet.{u}}
    {I : Type v} [SmallCategory I] [HasColimitsOfShape I (Over B)]
    (D : I ⥤ Over B ⥤ Over B)
    [∀ i, PreservesFilteredColimitsOfSize.{u, u} (D.obj i)] :
    PreservesFilteredColimitsOfSize.{u, u} (colimit D) where
  preserves_filtered_colimits J _ _ := by
    have : PreservesColimitsOfShape J D.flip :=
      preservesColimitsOfShape_of_evaluation D.flip J (fun i ↦ by
        change PreservesColimitsOfShape J (D.obj i)
        infer_instance)
    have : PreservesColimitsOfShape J (D.flip ⋙ colim) := inferInstance
    exact preservesColimitsOfShape_of_natIso (colimitFlipIsoCompColim D.flip).symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
