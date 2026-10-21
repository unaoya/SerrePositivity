module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativePath

/-!
概要：相対経路の同じ底を持つ実二端点を、代数的 pullback に束ねる。
方針：底への二つの厳密な合成式から、実代数射の普遍性を使う。
規約：相対端点射の全射性は未仮定。使われ方：全射準同型に対する持ち上げ比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativePath
variable (R : Type u) [CommRing R] {C B : Mon (Complex R)} (p : C ⟶ B)

def endpoints : Mon (Complex R) := MonoidPullback.obj p p

def endpointsSource : endpoints R p ⟶ C := MonoidPullback.fst p p

def endpointsTarget : endpoints R p ⟶ C := MonoidPullback.snd p p

lemma endpoints_condition : endpointsSource R p ≫ p = endpointsTarget R p ≫ p :=
  MonoidPullback.condition p p

def endpointsLift {A : Mon (Complex R)} (f g : A ⟶ C) (h : f ≫ p = g ≫ p) :
    A ⟶ endpoints R p := MonoidPullback.lift p p f g h

@[reassoc]
lemma endpointsLift_source {A : Mon (Complex R)} (f g : A ⟶ C) (h : f ≫ p = g ≫ p) :
    endpointsLift R p f g h ≫ endpointsSource R p = f := MonoidPullback.lift_fst _ _ _ _ _

@[reassoc]
lemma endpointsLift_target {A : Mon (Complex R)} (f g : A ⟶ C) (h : f ≫ p = g ≫ p) :
    endpointsLift R p f g h ≫ endpointsTarget R p = g := MonoidPullback.lift_snd _ _ _ _ _

def endpointsMap : algebra R p ⟶ endpoints R p :=
  MonoidPullback.lift p p (source R p) (target R p)
    ((source_projection R p).trans (target_projection R p).symm)

@[reassoc]
lemma endpointsMap_source : endpointsMap R p ≫ endpointsSource R p = source R p :=
  MonoidPullback.lift_fst _ _ _ _ _

@[reassoc]
lemma endpointsMap_target : endpointsMap R p ≫ endpointsTarget R p = target R p :=
  MonoidPullback.lift_snd _ _ _ _ _

def endpointsDiagonal : C ⟶ endpoints R p := MonoidPullback.lift p p (𝟙 C) (𝟙 C) rfl

lemma endpointsDiagonal_source : endpointsDiagonal R p ≫ endpointsSource R p = 𝟙 C :=
  MonoidPullback.lift_fst _ _ _ _ _

lemma endpointsDiagonal_target : endpointsDiagonal R p ≫ endpointsTarget R p = 𝟙 C :=
  MonoidPullback.lift_snd _ _ _ _ _

lemma diagonal_endpointsMap : diagonal R p ≫ endpointsMap R p = endpointsDiagonal R p := by
  apply MonoidPullback.hom_ext p p
  · change (diagonal R p ≫ endpointsMap R p) ≫ endpointsSource R p = _
    rw [Category.assoc, endpointsMap_source, diagonal_source]
    exact (endpointsDiagonal_source R p).symm
  · change (diagonal R p ≫ endpointsMap R p) ≫ endpointsTarget R p = _
    rw [Category.assoc, endpointsMap_target, diagonal_target]
    exact (endpointsDiagonal_target R p).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativePath
