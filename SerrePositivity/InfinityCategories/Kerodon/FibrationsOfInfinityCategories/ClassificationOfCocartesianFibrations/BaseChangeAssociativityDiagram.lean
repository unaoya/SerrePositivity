module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeAssociativityNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportBaseChangeCoherent

/-!
概要：二重底変換の同じ結合同型を底全体の図式の比較へ束ねる。
方針：元の成分の厳密な自然性を QCat 値自然変換に渡し、同じ比較を実現する。
規約：二回の元の底変換比較と直接の比較は、図式全体で厳密に一致する。
使われ方：底変換の比較 span の合成と区間の Segal 制限の整合性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  {E : SSet.{u}} (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (l : A ⥤ D) (k : D ⥤ C)

/-- 二重底変換の同じ結合同型を、元の QCat 値図式の自然変換へ束ねる。 -/
def cocartesianBaseChangeAssociativityQCat :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportQCatFunctor
        (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportQCatFunctor (pullback.fst (nerveMap (l ⋙ k)) p) where
  app a := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent p l k a).hom
  naturality a b f := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent_naturality p l k f

/-- 同じ結合同型の自然変換の各成分は、元の同型として同値。 -/
lemma cocartesianBaseChangeAssociativityQCat_isQCatEquivalence (a : A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((cocartesianBaseChangeAssociativityQCat p l k).app a) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent p l k a)).isQCatEquivalence

/-- 同じ結合同型は、二重底変換と直接の底変換の元の coherent 図式全体の同型。 -/
def cocartesianBaseChangeAssociativityCoherentIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram
        (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram (pullback.fst (nerveMap (l ⋙ k)) p)) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramFunctorIsoOfPointwise (cocartesianBaseChangeAssociativityQCat p l k)
    (cocartesianBaseChangeAssociativityQCat_isQCatEquivalence p l k)

/-- 二回の元の底変換比較と直接の比較は、同じ結合同型を通すと図式全体で一致する。 -/
lemma cocartesianStrictTransportBaseChangeQCat_comp :
    (Functor.whiskerLeft l (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeQCat p k) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeQCat (pullback.fst (nerveMap k) p) l) ≫
        cocartesianBaseChangeAssociativityQCat p l k =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeQCat p (l ⋙ k) := by
  ext a
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent_comp p l k a

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
