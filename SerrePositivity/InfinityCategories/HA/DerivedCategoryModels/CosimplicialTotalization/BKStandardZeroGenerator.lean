module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKStandardWeight
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBousfieldKanSetCone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone

/-!
概要：指定BKから標準重みへの零次比較は、恒等射の頂点を第0頂点の生成元へ送る。
方針：元のunder/overの逆比較と先頭頂点の評価を第0項で計算する。
規約：IS-W2 C01の既存重み構成の単位・評価則。頂点の選択を変更しない。
使われ方：HA 1.2.4、native Tot錐の同じ標準脚の最終計算。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 指定bar/over比較の零次の恒等生成元の像は、元の第0頂点の生成元。 -/
theorem barOverStandard_zero_generator (n : SimplexCategory) :
    let j := op (op n)
    (((barDoubleOppositeOverChainIso SimplexCategory (ModuleCat.of A A)).inv.f 0 ≫
      ((alternatingFaceMapComplex _).map
        (SimplicialRealization.barStandardWeightComparison (ModuleCat.of A A))).f 0).app j)
      (Sigma.ι (fun _ : (bousfieldKanSetWeight.obj (op ⦋0⦌)).obj j => ModuleCat.of A A)
        (nerveVertex (Over.mk (𝟙 n))) (1 : A)) =
    Sigma.ι (fun _ : op n ⟶ op ⦋0⦌ => ModuleCat.of A A)
      (SimplexCategory.const ⦋0⦌ n 0).op (1 : A) := by
  simp [barDoubleOppositeOverChainIso, reindexedBarOverChainIso,
    reindexedCoefficientBarWeightIso, alternatingFaceReverseIso,
    alternatingFaceReverseDegreeIso, alternatingFaceReverseSign,
    SimplicialRealization.barStandardWeightComparison, copowerFunctor]
  erw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply]
  simp only [Sigma.ι_comp_map'_assoc, Sigma.ι_comp_map']
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
