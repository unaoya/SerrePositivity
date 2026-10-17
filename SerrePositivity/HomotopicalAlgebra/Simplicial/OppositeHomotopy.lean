module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ExtraDegeneracyContraction

/-! # Reversing the simplex direction reverses interval homotopies -/

@[expose] public section
universe v uH vH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.OppositeHomotopy

abbrev reverse (X : SSet.{v}) : SSet.{v} := SimplexCategory.rev.op ⋙ X
abbrev reverseMap {X Y : SSet.{v}} (f : X ⟶ Y) : reverse X ⟶ reverse Y :=
  Functor.whiskerLeft SimplexCategory.rev.op f

abbrev intervalIso : reverse SimplexPrefix.interval.{v} ≅ SimplexPrefix.interval.{v} :=
  SSet.stdSimplex.opIso (SimplexCategory.mk 1)

def cylinderMap (X : SSet.{v}) : reverse X ⊗ SimplexPrefix.interval ⟶
    reverse (X ⊗ SimplexPrefix.interval) where
  app n := ↾fun x => (x.1, intervalIso.inv.app n x.2)
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · rfl
    · exact types_congr_hom (intervalIso.inv.naturality θ) x.2

lemma cylinderMap_zero (X : SSet.{v}) :
    SSet.ι₀ ≫ cylinderMap X = reverseMap (SSet.ι₁ (X := X)) := by
  ext n x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro j
    rfl

lemma cylinderMap_one (X : SSet.{v}) :
    SSet.ι₁ ≫ cylinderMap X = reverseMap (SSet.ι₀ (X := X)) := by
  ext n x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro j
    rfl

def homotopy {X Y : SSet.{v}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    SSet.Homotopy (reverseMap g) (reverseMap f) where
  h := cylinderMap X ≫ reverseMap H.h
  h₀ := by rw [← Category.assoc, cylinderMap_zero]; exact congrArg reverseMap H.h₁
  h₁ := by rw [← Category.assoc, cylinderMap_one]; exact congrArg reverseMap H.h₀
  rel := by
    apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

abbrev doubleIso (X : SSet.{v}) : reverse (reverse X) ≅ X :=
  SSet.opFunctorCompOpFunctorIso.app X

variable {A : SimplicialObject.Augmented (Type v)}
  (ed : SimplicialObject.Augmented.ExtraDegeneracy A)
  {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
def reversedComparisonIso : L.obj (reverse A.left) ≅
    L.obj (reverse ((SimplicialObject.const (Type v)).obj A.right)) :=
  AnodyneHomotopy.mapRetractionIso L hL (reverseMap A.hom) (reverseMap ed.section_)
    (congrArg reverseMap ed.section_comp_hom)
    (homotopy (ExtraDegeneracyContraction.contraction ed))

include ed in
lemma localized_reversed_augmentation_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (reverseMap A.hom)) :=
  (reversedComparisonIso ed AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)).isIso_hom

end SerrePositivity.SimplicialModel.OppositeHomotopy
