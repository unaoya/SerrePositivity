module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatSimplicial
/-!
概要：指定同値で可換な四角形を、同じ指定逆による四角形へ移す。
方針：元の全関手同型を逆で挟み、指定された往復同型を合成する。
規約：逆と往復則を選び直さない。使われ方：元二脚と固定入力の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory SSet
variable {X Y X' Y' : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  [Quasicategory X'] [Quasicategory Y']

def equivalenceSquareInverse (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X X') (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence Y Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ b.hom) (a.hom ≫ g)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (a.inv ≫ f) (g ≫ b.inv) := by
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (a.inv ≫ f) (a.inv ≫ f ≫ b.hom ≫ b.inv) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, Category.assoc, Category.comp_id] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp b.homInvIso.symm (a.inv ≫ f)
  have h₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (a.inv ≫ f ≫ b.hom ≫ b.inv)
      (a.inv ≫ a.hom ≫ g ≫ b.inv) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, Category.assoc] using
      (h.precomp a.inv).postcomp b.inv
  have h₃ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (a.inv ≫ a.hom ≫ g ≫ b.inv) (g ≫ b.inv) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, Category.assoc, Category.id_comp] using
      a.invHomIso.postcomp (g ≫ b.inv)
  exact h₁.trans (h₂.trans h₃)

def equivalenceSquareTwoInverse
    {P Q P' Q' : SSet.{u}} [Quasicategory P] [Quasicategory Q]
    [Quasicategory P'] [Quasicategory Q']
    (dD : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence P P') (dE : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence Q Q')
    (eD : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X P) (eE : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence Y Q)
    (f : P ⟶ Q) (g : P' ⟶ Q') (k : X ⟶ Y)
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ dE.hom) (dD.hom ≫ g))
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (eD.hom ≫ f) (k ≫ eE.hom)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (g ≫ (dE.symm.trans eE.symm).hom)
      ((dD.symm.trans eD.symm).hom ≫ k) := by
  have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (equivalenceSquareInverse dD dE f g hd).symm eE.inv
  have h₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (equivalenceSquareInverse eD eE k f he.symm).symm dD.inv
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.trans, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.symm, Category.assoc] using
    h₁.trans (by simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, Category.assoc] using h₂)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
