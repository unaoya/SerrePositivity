module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.SpecifiedProjectiveCocone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ComplexDerivedSemifreeComparison

/-!
概要：半自由から射影的模型へ進んで戻る同じ一点比較の単位を公開する。
方針：既存の同じ準圏同値のhomInvIsoを後合成する。
規約：新しい逆関手を選ばない。
使われ方：3b-3 R6 U31の単位の前提計算。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]

/-- U31の前提計算：既存の射影的一点比較は半自由入力上で同じ一点評価になる。 -/
def semifreeProjectivePointUnitIso :
    FunctorIso
      (SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (dgSemifreeToProjective A PUnit.{1}) ≫ (projectivePointEquivalence A).hom)
      (semifreePointEquivalence A).hom := by
  let e := (dgSemifreeToProjectiveNerve_isQCatEquivalence A PUnit.{1}).choose
  change FunctorIso (e.hom ≫ e.inv ≫ (semifreePointEquivalence A).hom)
    (semifreePointEquivalence A).hom
  simpa only [Category.assoc, Category.id_comp] using!
    e.homInvIso.postcomp (semifreePointEquivalence A).hom

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
