module

public import SerrePositivity.HomotopicalAlgebra.Quillen.DerivedFunctor

/-! # Extending a natural comparison on cofibrant representatives

The composite of the cofibrant inclusion and any ordinary localization is
itself a localization. A comparison of functors after that composite thus
extends to the whole localized category, without chosen factorizations.
-/

@[expose] public section
universe v u vH uH vD uD
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Quillen
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type uH} [Category.{vH} H] {D : Type uD} [Category.{vD} D]
  (Q : C ⥤ H) [Q.IsLocalization (weakEquivalences C)] {F G : H ⥤ D}

def isoOfCofibrantComparison
    (e : (CofibrantObject.ι ⋙ Q) ⋙ F ≅ (CofibrantObject.ι ⋙ Q) ⋙ G) : F ≅ G :=
  Localization.liftNatIso (CofibrantObject.ι ⋙ Q) (weakEquivalences (CofibrantObject C))
    _ _ F G e

@[simp] lemma isoOfCofibrantComparison_hom_app
    (e : (CofibrantObject.ι ⋙ Q) ⋙ F ≅ (CofibrantObject.ι ⋙ Q) ⋙ G)
    (X : C) [IsCofibrant X] :
    (isoOfCofibrantComparison Q e).hom.app (Q.obj X) = e.hom.app (CofibrantObject.mk X) := by
  change (Localization.liftNatTrans (CofibrantObject.ι ⋙ Q)
    (weakEquivalences (CofibrantObject C)) _ _ F G e.hom).app
      ((CofibrantObject.ι ⋙ Q).obj (CofibrantObject.mk X)) = _
  rw [Localization.liftNatTrans_app]
  simp

end SerrePositivity.Quillen
