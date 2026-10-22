module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCoefficientComposition

/-!
概要：同じ底の平方零代数構成を、実双加群の圏上の関手として供給する。
方針：元の係数射と検証済みの合成式を使い、同型も元の二つの係数射から移す。
規約：底と係数を保持。使われ方：class 標的の実同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] (A : Mon (Complex R))

def coefficientFunctor : Bimod A A ⥤ Mon (Complex R) where
  obj M := algebra A M
  map f := coefficientMap A f
  map_id M := by
    apply Mon.Hom.ext
    change biprod.map (𝟙 A.X) (𝟙 M.X) = 𝟙 (A.X ⊞ M.X)
    apply biprod.hom_ext <;> simp
  map_comp f g := (coefficientMap_comp f g).symm

def coefficientIso {M N : Bimod A A} (e : M ≅ N) : algebra A M ≅ algebra A N :=
  (coefficientFunctor A).mapIso e

lemma coefficientIso_hom {M N : Bimod A A} (e : M ≅ N) :
    (coefficientIso A e).hom = coefficientMap A e.hom := rfl

end SerrePositivity.KST.LocalizingInvariants.SquareZero
