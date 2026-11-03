module

public import SerrePositivity.InfinityCategories.F2.Presentable.RepresentableSmallFibers
public import SerrePositivity.InfinityCategories.F2.Presentable.RepresentabilityEquivalence
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessibleIndRepresentation
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallFiberStraightening
public import SerrePositivity.InfinityCategories.F1.Yoneda.RepresentablePresheafSliceComparison
public import SerrePositivity.InfinityCategories.F1.Compact.UniverseUnstraightening

/-!
概要：accessible 圏の元の各対象への反変 Hom を小さい空間値の全関手で表す。
方針：Ind 模型の表現可能射影を小さい fiber の straightening で分類し、同値で戻す。
規約：元の全表現可能前層との自然同型を持ち、点ごとの Hom の選択には置き換えない。
使われ方：表現可能性から右随伴を構成するための小さい Hom 模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：固定頂点写像が小さい圏の元の全反変 Hom は小さい空間値の模型を持つ。
方針：反転した元の slice の小さい次数 fiber を分類し、同じ宇宙変更と比較する。
規約：表現対象と元の全 Yoneda 前層を保持する。
使われ方：Ind 圏の小さい反変 Hom 模型。 -/
lemma exists_smallContravariantHom_of_fixedVertexMaps
    {C : SSet.{u + 1}} [Quasicategory C]
    (hC : Ind.HasSmallFixedVertexMaps C) (y : C _⦋0⦌) :
    ∃ H : C.op ⟶ SpaceInfinity.{u}, Nonempty (FunctorIso (representablePresheafInfinity y)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map H ≫ Compact.spaceUniverseDiagram)) := by
  let p := SSet.opFunctor.map (sliceOverProjection (SSet.yonedaEquiv.symm y))
  have hp : HasSmallSimplexFibers p :=
    smallSimplexFibers_op (representable_hasSmallSimplexFibers hC y)
  let H := smallFiberLeftStraighteningDiagram p hp
  refine ⟨H, ⟨?_⟩⟩
  exact representablePresheafInfinity_sliceIso y ≪≫
    Compact.leftClassification_of_precompositionEquivalence p
      (leftUnstraighteningProjection H) (smallFiberLeftStraighteningComparison p hp)
      (smallFiberLeftStraighteningComparison_over_base p hp)
      (smallFiberLeftStraighteningComparison_isPrecompositionEquivalence p hp) ≪≫
    Compact.spaceUniverseUnstraightening_classificationIso H

/-- 概要：accessible 圏の元の各対象への全反変 Hom は小さい空間値の模型を持つ。
方針：Ind 同値の逆に沿って小さい模型を引き戻し、充満忠実な全 Yoneda 比較を合成する。
規約：同値の像に対象を置き換えず、元の対象の表現可能前層と比較する。
使われ方：余極限保存関手の Hom 合成を小さい空間値で扱う。 -/
lemma IsAccessible.exists_smallContravariantHom {C : SSet.{u + 1}} [Quasicategory C]
    (hC : IsAccessible C) (y : C _⦋0⦌) :
    ∃ H : C.op ⟶ SpaceInfinity.{u}, Nonempty (FunctorIso (representablePresheafInfinity y)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map H ≫ Compact.spaceUniverseDiagram)) := by
  obtain ⟨κ, hκ⟩ := hC
  obtain ⟨A, hA, ⟨e⟩⟩ := hκ.exists_indEquivalence
  have := hA
  obtain ⟨H, ⟨hH⟩⟩ := exists_smallContravariantHom_of_fixedVertexMaps
    (Ind.ind_hasSmallFixedVertexMaps κ A) (e.inv.app (Opposite.op ⦋0⦌) y)
  refine ⟨SSet.opFunctor.map e.inv ≫ H, ⟨?_⟩⟩
  have h := fullyFaithfulRepresentableRestrictionIso e.inv
    e.symm.isQCatEquivalence.isFullyFaithful y ≪≫
    FunctorIso.precomp hH
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map e.inv))
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using h

end SerrePositivity.InfinityCategories.F2.Presentable
