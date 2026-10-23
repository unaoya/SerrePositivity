module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexSegal
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalDiagramTwoSimplexSegal
public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackRestrictionNaturality

/-!
概要：二次元 Segal 比較の両射影は、元の二つの区間への直接の制限。
方針：ホーンを経由する制限を、元の底上の自然性で合成する。
規約：元の分類 Hom 作用の両側で同じ二包含を保持する。
使われ方：底変換の比較 span と Segal 比較の整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open InnerTwoHornOver

/-- 元の Hom の Segal 比較の最初の射影は、次の区間への直接の制限。 -/
lemma cocartesianTwoSimplexSegalMap_fst_restriction
    {E F : SSet.{u}} (p : E ⟶ (Δ[2] : SSet.{u})) [CocartesianFibration p]
    (q : F ⟶ (Δ[2] : SSet.{u})) [CocartesianFibration q] :
    cocartesianTwoSimplexSegalMap p q ≫ pullback.fst _ _ =
      quasicategoryCoreMap (cocartesianPullbackNativeRestriction p q
        (second (horn 2 1).ι)) := by
  rw [cocartesianTwoSimplexSegalMap_fst]
  change quasicategoryCoreFunctor.map _ ≫ quasicategoryCoreFunctor.map _ = _
  rw [← Functor.map_comp, cocartesianPullbackNativeRestriction_naturality]
  rfl

/-- 元の Hom の Segal 比較の二番目の射影は、最初の区間への直接の制限。 -/
lemma cocartesianTwoSimplexSegalMap_snd_restriction
    {E F : SSet.{u}} (p : E ⟶ (Δ[2] : SSet.{u})) [CocartesianFibration p]
    (q : F ⟶ (Δ[2] : SSet.{u})) [CocartesianFibration q] :
    cocartesianTwoSimplexSegalMap p q ≫ pullback.snd _ _ =
      quasicategoryCoreMap (cocartesianPullbackNativeRestriction p q
        (first (horn 2 1).ι)) := by
  rw [cocartesianTwoSimplexSegalMap_snd]
  change quasicategoryCoreFunctor.map _ ≫ quasicategoryCoreFunctor.map _ = _
  rw [← Functor.map_comp, cocartesianPullbackNativeRestriction_naturality]
  rfl

/-- 分類先の Segal 比較の最初の射影も、同じ次の区間への直接の制限。 -/
lemma intervalDiagramTwoSimplexSegalMap_fst_restriction {X : SSet.{u}}
    (F G : (Δ[2] : SSet.{u}) ⟶ X) :
    intervalDiagramTwoSimplexSegalMap F G ≫
        pullback.fst (intervalDiagramOverPre F G (toSecond (horn 2 1).ι))
          (intervalDiagramOverPre F G (toFirst (horn 2 1).ι)) =
      intervalDiagramRestriction (second (horn 2 1).ι).hom F G := by
  rw [intervalDiagramTwoSimplexSegalMap_fst]
  exact intervalDiagramOverPre_restriction F G (secondInclusion (horn 2 1).ι)

/-- 分類先の Segal 比較の二番目の射影も、同じ最初の区間への直接の制限。 -/
lemma intervalDiagramTwoSimplexSegalMap_snd_restriction {X : SSet.{u}}
    (F G : (Δ[2] : SSet.{u}) ⟶ X) :
    intervalDiagramTwoSimplexSegalMap F G ≫
        pullback.snd (intervalDiagramOverPre F G (toSecond (horn 2 1).ι))
          (intervalDiagramOverPre F G (toFirst (horn 2 1).ι)) =
      intervalDiagramRestriction (first (horn 2 1).ι).hom F G := by
  rw [intervalDiagramTwoSimplexSegalMap_snd]
  exact intervalDiagramOverPre_restriction F G (firstInclusion (horn 2 1).ι)

end SerrePositivity.InfinityCategories
