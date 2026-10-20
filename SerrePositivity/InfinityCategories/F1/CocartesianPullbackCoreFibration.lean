module

public import SerrePositivity.InfinityCategories.F1.CocartesianPullbackNativeFunctor
public import SerrePositivity.InfinityCategories.F1.MarkedCocartesianFunctorRestrictionLifting

/-!
概要：底の単射による、元の各底変換の cocartesian Hom の core の制限は Kan fibration。
方針：始域の引き戻しの単射性と指定辺の保存を使い、同じ厳密な Hom 同型で移す。
規約：底の単射の同値性や、可変の底の quasicategory 性を要求しない。
使われ方：セルの境界・骨格での元の Hom の core の降下の充填性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories

variable {E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q]
  {a b : Over B} (f : a ⟶ b) [Mono f.left]

/-- 底の単射による局所 Hom の core の同じ制限は Kan fibration。 -/
lemma core_cocartesianPullbackHomPre_fibration :
    Fibration (quasicategoryCoreMap (cocartesianPullbackHomPre p q f)) := by
  letI : Mono f := Over.mono_of_mono_left f
  letI : Mono ((Over.pullback p ⋙ Over.map p).map f).left :=
    inferInstanceAs (Mono ((overPullbackUnderlying p).map f))
  exact core_markedCocartesianFunctorPre_fibration q
    ((Over.pullback p ⋙ Over.map p).map f) _ _
    (fun e he ↦ isCocartesianEdge_overPullback_map p f e he)

/-- 底の単射による元の各底変換の cocartesian Hom の core の制限は Kan fibration。 -/
lemma core_cocartesianPullbackNativePre_fibration :
    Fibration (quasicategoryCoreMap (cocartesianPullbackNativePre p q f)) := by
  haveI : Fibration (quasicategoryCoreFunctor.map (cocartesianPullbackHomPre p q f)) :=
    core_cocartesianPullbackHomPre_fibration p q f
  haveI : IsIso (quasicategoryCoreFunctor.map (cocartesianPullbackHomIso p q b).hom) :=
    inferInstanceAs (IsIso (quasicategoryCoreFunctor.mapIso
      (cocartesianPullbackHomIso p q b)).hom)
  haveI : IsIso (quasicategoryCoreFunctor.map (cocartesianPullbackHomIso p q a).inv) :=
    inferInstanceAs (IsIso (quasicategoryCoreFunctor.mapIso
      (cocartesianPullbackHomIso p q a)).inv)
  change Fibration (quasicategoryCoreFunctor.map
    ((cocartesianPullbackHomIso p q b).hom ≫ cocartesianPullbackHomPre p q f ≫
      (cocartesianPullbackHomIso p q a).inv))
  rw [quasicategoryCoreFunctor.map_comp, quasicategoryCoreFunctor.map_comp]
  infer_instance

end SerrePositivity.InfinityCategories
