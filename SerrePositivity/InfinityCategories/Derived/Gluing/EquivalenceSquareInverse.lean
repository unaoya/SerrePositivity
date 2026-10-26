module
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoTransport
public import SerrePositivity.InfinityCategories.F1.Categories.QCatSimplicial
/-!
概要：指定同値で可換な四角形を、同じ指定逆による四角形へ移す。
方針：元の全関手同型を逆で挟み、指定された往復同型を合成する。
規約：逆と往復則を選び直さない。使われ方：元二脚と固定入力の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Derived.Gluing
open CategoryTheory SSet
variable {X Y X' Y' : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  [Quasicategory X'] [Quasicategory Y']

def equivalenceSquareInverse (a : QCatEquivalence X X') (b : QCatEquivalence Y Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (h : FunctorIso (f ≫ b.hom) (a.hom ≫ g)) :
    FunctorIso (a.inv ≫ f) (g ≫ b.inv) := by
  have h₁ : FunctorIso (a.inv ≫ f) (a.inv ≫ f ≫ b.hom ≫ b.inv) := by
    simpa only [FunctorIso, Category.assoc, Category.comp_id] using
      FunctorIso.precomp b.homInvIso.symm (a.inv ≫ f)
  have h₂ : FunctorIso (a.inv ≫ f ≫ b.hom ≫ b.inv)
      (a.inv ≫ a.hom ≫ g ≫ b.inv) := by
    simpa only [FunctorIso, Category.assoc] using
      (h.precomp a.inv).postcomp b.inv
  have h₃ : FunctorIso (a.inv ≫ a.hom ≫ g ≫ b.inv) (g ≫ b.inv) := by
    simpa only [FunctorIso, Category.assoc, Category.id_comp] using
      a.invHomIso.postcomp (g ≫ b.inv)
  exact h₁.trans (h₂.trans h₃)

def equivalenceSquareTwoInverse
    {P Q P' Q' : SSet.{u}} [Quasicategory P] [Quasicategory Q]
    [Quasicategory P'] [Quasicategory Q']
    (dD : QCatEquivalence P P') (dE : QCatEquivalence Q Q')
    (eD : QCatEquivalence X P) (eE : QCatEquivalence Y Q)
    (f : P ⟶ Q) (g : P' ⟶ Q') (k : X ⟶ Y)
    (hd : FunctorIso (f ≫ dE.hom) (dD.hom ≫ g))
    (he : FunctorIso (eD.hom ≫ f) (k ≫ eE.hom)) :
    FunctorIso (g ≫ (dE.symm.trans eE.symm).hom)
      ((dD.symm.trans eD.symm).hom ≫ k) := by
  have h₁ := FunctorIso.postcomp (equivalenceSquareInverse dD dE f g hd).symm eE.inv
  have h₂ := FunctorIso.precomp (equivalenceSquareInverse eD eE k f he.symm).symm dD.inv
  simpa only [FunctorIso, QCatEquivalence.trans, QCatEquivalence.symm, Category.assoc] using
    h₁.trans (by simpa only [FunctorIso, Category.assoc] using h₂)

end SerrePositivity.InfinityCategories.Derived.Gluing
