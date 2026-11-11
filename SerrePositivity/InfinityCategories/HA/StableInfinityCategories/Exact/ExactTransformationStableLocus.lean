module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.FullStableClosure
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorNaturalTransformation

/-!
概要：完全関手間の実自然変換の成分が可逆である頂点条件は安定閉性を持つ。
方針：h の distinguished triangle 間の元の自然変換の三成分に二つから三つ目の判定を使う。
規約：関手の完全性は実 cofiber 保存による。使われ方：通常 pullback の頂点条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact
open _root_.SerrePositivity.KST.LocalizingInvariants

variable {X Y : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]
  {F G : X ⟶ Y} [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor G]
  (H : SSet.Homotopy F G)

def TransformationIsoVertex (x : X _⦋0⦌) : Prop :=
  IsIso ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorNatTrans H).app (HomotopyCategory.mk x))

/-- 三角形の成分の二つから三つ目の同型性を元の頂点条件へ戻す。 -/
lemma transformationIsoVertex_stable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.StableVertexCondition (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.TransformationIsoVertex H) where
  zero x hx := by
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := F) x hx).isZeroHo.isIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := G) x hx).isZeroHo _
  cofiber t ht h₀ h₁ := by
    let T := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht
    let a := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorNatTransTriangle H).app T
    have hT := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle_mem_cofiberDistinguishedTriangles t ht
    exact Pretriangulated.isIso₃_of_isIso₁₂ a
      ((hoFunctor.map F).toFunctor.map_distinguished T hT)
      ((hoFunctor.map G).toFunctor.map_distinguished T hT) h₀ h₁
  fiber t ht h₁ h₂ := by
    have hc := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pushout_of_pullback t ht
    let T := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t hc
    let a := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorNatTransTriangle H).app T
    have hT := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle_mem_cofiberDistinguishedTriangles t hc
    exact Pretriangulated.isIso₁_of_isIso₂₃ a
      ((hoFunctor.map F).toFunctor.map_distinguished T hT)
      ((hoFunctor.map G).toFunctor.map_distinguished T hT) h₁ h₂

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.TransformationIsoVertex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.TransformationIsoVertex := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.TransformationIsoVertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.transformationIsoVertex_stable := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.transformationIsoVertex_stable
