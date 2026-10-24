module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldPullbackMarkedRestriction
public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackCoreFibration

/-!
概要：部分底上の辺保存 scaffold core の自然性と単射制限の Kan 性。
方針：辺保存 Hom の自然性を core 関手で移し、引き戻しの単射性で充填を制限する。
規約：部分底の quasicategory 性は要求しない。
使われ方：同じ境界値の fiber の比較同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] {E F : SSet.{u}}
  (p : E ⟶ nerve C) [CocartesianFibration p] (q : F ⟶ nerve C)
  {a b : Over (nerve C)} (f : a ⟶ b)

/-- 同じ辺保存 scaffold core の底の制限。 -/
def cocartesianScaffoldPullbackMarkedCoreRestriction :=
  quasicategoryCoreMap (cocartesianScaffoldPullbackMarkedHomPre p q f)

/-- 同じ元の core 比較は、底の制限と厳密に可換。 -/
lemma cocartesianScaffoldPullbackMarkedCorePre_naturality :
    cocartesianScaffoldPullbackMarkedCorePre p q b ≫
      cocartesianScaffoldPullbackMarkedCoreRestriction p q f =
    quasicategoryCoreMap (cocartesianPullbackHomPre p q f) ≫
      cocartesianScaffoldPullbackMarkedCorePre p q a := by
  change quasicategoryCoreFunctor.map _ ≫ quasicategoryCoreFunctor.map _ =
    quasicategoryCoreFunctor.map _ ≫ quasicategoryCoreFunctor.map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    cocartesianScaffoldPullbackMarkedPre_naturality]

/-- 部分底の単射による同じ scaffold core 制限は Kan fibration。 -/
lemma cocartesianScaffoldPullbackMarkedCoreRestriction_fibration
    [CocartesianFibration q] [Mono f.left] :
    Fibration (cocartesianScaffoldPullbackMarkedCoreRestriction p q f) := by
  let r := simplicialReplacementProjection (SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram p)
  letI : Mono f := Over.mono_of_mono_left f
  letI : Mono ((Over.pullback r ⋙ Over.map r).map f).left :=
    inferInstanceAs (Mono ((overPullbackUnderlying r).map f))
  exact core_markedCocartesianFunctorPre_fibration q
    ((Over.pullback r ⋙ Over.map r).map f) _ _
    (cocartesianScaffoldPullbackMark_map p f)

end SerrePositivity.InfinityCategories
