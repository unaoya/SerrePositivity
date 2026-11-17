module
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.KanHomFamilyOpposite
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
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

/-- 元のnerveの反転同型を、同じ全係数の自然変換として記録する。 -/
def catNerveOppositeFamilyMap :
    (F ⋙ nerveFunctor) ⋙ SSet.opFunctor ⟶ (F ⋙ Cat.opFunctor) ⋙ nerveFunctor where
  app _ :=  nerveOppositeMap
  naturality _ _ f := nerveOppositeMap_naturality (F.map f).toFunctor

/-- 同じnerveの反転同型の全成分は元の射として弱同値。 -/
lemma catNerveOppositeFamilyMap_weak (i : I) :
    IsWeakHomotopyEquivalence ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.catNerveOppositeFamilyMap F).app i) :=
  (qCatEquivalenceOfIso (nerveOppositeIso (C := F.obj i))).isQCatEquivalence.isWeakHomotopyEquivalence

/-- 元のnerveの反転同型のKan化を全関手同型にする。 -/
def catNerveOppositeFamilyUnitIso :
    FunctorIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyCoherent ((F ⋙ nerveFunctor) ⋙ SSet.opFunctor))
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyCoherent ((F ⋙ Cat.opFunctor) ⋙ nerveFunctor)) :=
  kanDiagramFunctorIsoOfPointwise
    (F := ⟨_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamily ((F ⋙ nerveFunctor) ⋙ SSet.opFunctor), trivial⟩)
    (G := ⟨_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamily ((F ⋙ Cat.opFunctor) ⋙ nerveFunctor), trivial⟩)
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.catNerveOppositeFamilyMap F))
    (fun i => _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyMap_isQCatEquivalence _ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.catNerveOppositeFamilyMap_weak F) i)

/-- 同じ全Cat図式のnerveと反対圏のnerveはKan化後の全関手同型を持つ。 -/
def catNerveOppositeFamilyIso :
    FunctorIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyCoherent (F ⋙ nerveFunctor))
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyCoherent ((F ⋙ Cat.opFunctor) ⋙ nerveFunctor)) :=
  (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyOppositeComparisonIso (F ⋙ nerveFunctor)).trans
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.catNerveOppositeFamilyUnitIso F)
end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
