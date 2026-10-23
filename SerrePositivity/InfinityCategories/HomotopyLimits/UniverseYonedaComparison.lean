module

public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseYonedaJoint
public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafUniverseDiagram
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorSpaceCurrying

/-!
概要：指定された前層の宇宙変更は、元の全 Yoneda 関手を全自然同型として保つ。
方針：元の二変数 Hom 比較を curry し、同じ前層宇宙変更の全評価の式へ同定する。
規約：元の Yoneda 全写像と指定宇宙変更を保持する。
使われ方：元の大きい係数前層への自然変換空間の全族と、元の延長の Hom 全族の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable (C : SSet.{u}) [Quasicategory C]

omit [Quasicategory C] in
/-- 同じ共同 Hom の底比較は、元の前層の宇宙変更に現れる指定比較の合成。 -/
lemma homInfinityUniverseBaseMap_equation :
    homInfinityUniverseBaseMap C =
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (uliftOppositeIso.{u, u + 1} C).inv ▷
        (SSet.uliftFunctor.{u + 2, u + 1}).obj ((SSet.uliftFunctor.{u + 1, u}).obj C)) ≫
      (uliftTensorIso.{u + 1, u + 2}
        ((SSet.uliftFunctor.{u + 1, u}).obj C.op)
        ((SSet.uliftFunctor.{u + 1, u}).obj C)).inv ≫
      (SSet.uliftFunctor.{u + 2, u + 1}).map (uliftTensorIso.{u, u + 1} C.op C).inv := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 元の Yoneda の指定宇宙変更の共同評価は、同じ小さい共同 Hom の宇宙変更。 -/
lemma yonedaInfinityMap_universe_uncurry :
    uncurry ((SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaInfinityMap C) ≫
      presheafUniverseDiagram C) =
    homInfinityUniverseBaseMap C ≫
      (SSet.uliftFunctor.{u + 2, u + 1}).map (twistedArrowHomInfinity C) ≫
        F2.Compact.spaceUniverseDiagram.{u} := by
  dsimp only [presheafUniverseDiagram]
  rw [← Category.assoc, ← Category.assoc, uncurry_pre_app, uncurry_natural_right,
    uliftInternalHomComparison_map_uncurry, yonedaInfinityMap_uncurry,
    homInfinityUniverseBaseMap_equation]
  dsimp only [homInfinityJointEvaluation]
  simp only [Functor.map_comp, Category.assoc]

/-- 指定前層宇宙変更をした元の Yoneda 全関手は、持ち上げた元の圏の Yoneda と自然同型。 -/
def yonedaInfinityMap_universeIso :
    FunctorIso ((SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaInfinityMap C) ≫
      presheafUniverseDiagram C)
      (yonedaInfinityMap ((SSet.uliftFunctor.{u + 1, u}).obj C)) := by
  have e := FunctorIso.curry (homInfinityJointUniverseIso C).symm
  change FunctorIso (curry (homInfinityUniverseBaseMap C ≫
    (SSet.uliftFunctor.{u + 2, u + 1}).map (twistedArrowHomInfinity C) ≫
      F2.Compact.spaceUniverseDiagram.{u})) _ at e
  rw [← yonedaInfinityMap_universe_uncurry, curry_uncurry] at e
  exact e

end SerrePositivity.InfinityCategories.HomotopyLimits
