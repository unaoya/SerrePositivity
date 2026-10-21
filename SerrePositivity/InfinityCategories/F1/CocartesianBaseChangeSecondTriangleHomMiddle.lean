module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeSecondTriangleHomSecond
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeAssociativityHomSpan
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeHomSpan
public import SerrePositivity.InfinityCategories.F1.EquivalenceTriangleFaceEvaluation

/-!
概要：元の二回目の比較 Hom と元の結合比較 Hom は、同じ中間の分類 Hom を厳密に共有する。
方針：同じ分解三角形の中間頂点への二つの評価を照合する。
規約：元の二回の pullback 対象の分類図式を使う。
使われ方：元の第二面の Hom 輸送を実際の二段の輸送として結ぶ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ分解三角形の中間 Hom の二つの元の射影は厳密に一致する。 -/
lemma cocartesianBaseChangeSecondTriangleHom_middle
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    cocartesianBaseChangeSecondTriangleHomFirst l k p q ≫
        cocartesianBaseChangeHomSpanOne l
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q) =
      cocartesianBaseChangeSecondTriangleHomSecond l k p q ≫
        cocartesianBaseChangeAssociativityHomSpanZero l k p q := by
  have h : equivalenceTriangleFace
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) 2 ≫
        equivalencePathEndpoint _ 1 = equivalenceTriangleFace
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) 0 ≫
        equivalencePathEndpoint _ 0 := by
    rw [equivalenceTriangleFace_endpoint, equivalenceTriangleFace_endpoint]
    exact congrArg (equivalenceTriangleEvaluation _) (show
      (2 : Fin 3).succAbove (1 : Fin 2) = (0 : Fin 3).succAbove (0 : Fin 2) by decide)
  apply intervalMappingUncurry_injective
  rw [cocartesianBaseChangeHomSpanOne, intervalHomPathEndpoint_uncurry,
    cocartesianBaseChangeAssociativityHomSpanZero, intervalHomPathEndpoint_uncurry,
    cocartesianBaseChangeSecondTriangleHomFirst, intervalMappingPostOfEq_universal_uncurry,
    cocartesianBaseChangeSecondTriangleHomSecond, intervalHomFamilyProjection,
    intervalMappingPostOfEq_universal_uncurry]
  simpa only [Category.assoc, CatInfinityFunctor, cocartesianBaseChangeSecondTriangleHomSpace]
    using congrArg
    (fun f ↦ intervalMappingUncurry (𝟙 (cocartesianBaseChangeSecondTriangleHomSpace l k p q)) ≫ f) h

end SerrePositivity.InfinityCategories
