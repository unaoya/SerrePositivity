module

public import SerrePositivity.InfinityCategories.F1.CocartesianInnerTwoHornImageRestriction

/-!
概要：同型で表示した二次内ホーンへの元の全 Hom の core の制限は自明 Kan。
方針：元の指定辺保存 Hom の自明 Kan 性を core と同じ native Hom 同型へ移す。
規約：元の全 Hom の core を保持する。
使われ方：nerve 上の元の二単体の source Segal 制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {E F B : SSet.{u}} [Quasicategory B] (s : (Δ[2] : SSet.{u}) ≅ B)
  (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q]

/-- 元の同じ指定辺保存 Hom の core への制限も自明 Kan。 -/
lemma core_cocartesianPullbackHomRestriction_innerTwoHornImage_trivialKanFibration :
    TrivialKanFibration (quasicategoryCoreMap
      (cocartesianPullbackHomRestriction p q (Over.mk ((horn 2 1).ι ≫ s.hom)))) := by
  letI := cocartesianPullbackHomRestriction_innerTwoHornImage_trivialKanFibration s p q
  letI : Quasicategory (cocartesianPullbackHomSpace p q
      (Over.mk ((horn 2 1).ι ≫ s.hom))) := by
    unfold cocartesianPullbackHomSpace
    infer_instance
  exact F2.coreMap_trivialKanFibration _

/-- 元の両射影を底変換した native Hom の core への制限も同じ自明 Kan 射。 -/
lemma core_cocartesianPullbackNativeRestriction_innerTwoHornImage_trivialKanFibration :
    TrivialKanFibration (quasicategoryCoreMap
      (cocartesianPullbackNativeRestriction p q (Over.mk ((horn 2 1).ι ≫ s.hom)))) := by
  let a : Over B := Over.mk ((horn 2 1).ι ≫ s.hom)
  change TrivialKanFibration (quasicategoryCoreFunctor.map
    (cocartesianPullbackHomRestriction p q a ≫ (cocartesianPullbackHomIso p q a).inv))
  rw [CategoryTheory.Functor.map_comp]
  exact ⟨trivialKanFibrations.comp_mem _ _
    (core_cocartesianPullbackHomRestriction_innerTwoHornImage_trivialKanFibration s p q).mem
    (trivialKanFibrations.of_isIso _)⟩

end SerrePositivity.InfinityCategories
