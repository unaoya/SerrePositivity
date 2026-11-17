module
public import SerrePositivity.EInfinity.FrameHom.KanHomFamilyOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOpposite
public import Mathlib.CategoryTheory.Category.Cat.Op

/-!
概要：通常圏の全図式で、反対圏のnerveと元のnerveのKan係数を比較する。
方針：元のnerve反転同型の自然性を、既存のKan係数反転比較へ合成する。
規約：底とその全射を保ち、値の圏だけを反転する。
使われ方：元の全要素圏と反対要素圏の係数規約の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

/-- 元のnerveの反転同型を、同じ全係数の自然変換として記録する。 -/
def catNerveOppositeFamilyMap :
    (F ⋙ nerveFunctor) ⋙ SSet.opFunctor ⟶ (F ⋙ Cat.opFunctor) ⋙ nerveFunctor where
  app _ :=  nerveOppositeMap
  naturality _ _ f := nerveOppositeMap_naturality (F.map f).toFunctor

/-- 同じnerveの反転同型の全成分は元の射として弱同値。 -/
lemma catNerveOppositeFamilyMap_weak (i : I) :
    IsWeakHomotopyEquivalence ((catNerveOppositeFamilyMap F).app i) :=
  (qCatEquivalenceOfIso (nerveOppositeIso (C := F.obj i))).isQCatEquivalence.isWeakHomotopyEquivalence

/-- 元のnerveの反転同型のKan化を全関手同型にする。 -/
def catNerveOppositeFamilyUnitIso :
    FunctorIso (kanHomFamilyCoherent ((F ⋙ nerveFunctor) ⋙ SSet.opFunctor))
      (kanHomFamilyCoherent ((F ⋙ Cat.opFunctor) ⋙ nerveFunctor)) :=
  kanDiagramFunctorIsoOfPointwise
    (F := ⟨kanHomFamily ((F ⋙ nerveFunctor) ⋙ SSet.opFunctor), trivial⟩)
    (G := ⟨kanHomFamily ((F ⋙ Cat.opFunctor) ⋙ nerveFunctor), trivial⟩)
    (kanHomFamilyMap (catNerveOppositeFamilyMap F))
    (fun i => kanHomFamilyMap_isQCatEquivalence _ (catNerveOppositeFamilyMap_weak F) i)

/-- 同じ全Cat図式のnerveと反対圏のnerveはKan化後の全関手同型を持つ。 -/
def catNerveOppositeFamilyIso :
    FunctorIso (kanHomFamilyCoherent (F ⋙ nerveFunctor))
      (kanHomFamilyCoherent ((F ⋙ Cat.opFunctor) ⋙ nerveFunctor)) :=
  (kanHomFamilyOppositeComparisonIso (F ⋙ nerveFunctor)).trans
    (catNerveOppositeFamilyUnitIso F)
end SerrePositivity.EInfinity.FrameHom
