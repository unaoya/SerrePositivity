module

public import SerrePositivity.KST.LocalizingInvariants.CochainPullbackLift
public import SerrePositivity.KST.LocalizingInvariants.MonoidPullbackUniversal
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathFunctor

/-!
概要：一致する実経路の両端と比較 cochain を、元の代数 pullback へ持ち上げる。
方針：端点の自然性と比較 cochain の自然性を、実 pullback の二座標に渡す。
規約：比較 cochain も保持。使われ方：相対経路の共通底への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathPullback
variable (R : Type u) [CommRing R] {A B D W : Mon (Complex R)} (f : A ⟶ D) (g : B ⟶ D)
  (a : W ⟶ Path.algebra R A) (b : W ⟶ Path.algebra R B)
  (h : a ≫ Path.map R f = b ≫ Path.map R g)

include h in
lemma source_condition : (a ≫ Path.source R A) ≫ f = (b ≫ Path.source R B) ≫ g := by
  have hc := congrArg (fun t => t ≫ Path.source R D) h
  simpa only [Category.assoc, Path.map_source] using hc

include h in
lemma target_condition : (a ≫ Path.target R A) ≫ f = (b ≫ Path.target R B) ≫ g := by
  have hc := congrArg (fun t => t ≫ Path.target R D) h
  simpa only [Category.assoc, Path.map_target] using hc

def sourceLift : W ⟶ MonoidPullback.obj f g :=
  MonoidPullback.lift f g (a ≫ Path.source R A) (b ≫ Path.source R B)
    (source_condition R f g a b h)

def targetLift : W ⟶ MonoidPullback.obj f g :=
  MonoidPullback.lift f g (a ≫ Path.target R A) (b ≫ Path.target R B)
    (target_condition R f g a b h)

def leftPrimitive : Cochain W.X A.X (-1) :=
  (Cochain.ofHom a.hom).comp (Path.primitive R A) (zero_add (-1))
def rightPrimitive : Cochain W.X B.X (-1) :=
  (Cochain.ofHom b.hom).comp (Path.primitive R B) (zero_add (-1))

include h in
lemma primitive_condition : (leftPrimitive R a).comp (Cochain.ofHom f.hom) (add_zero (-1)) =
    (rightPrimitive R b).comp (Cochain.ofHom g.hom) (add_zero (-1)) := by
  have hc : a.hom ≫ Path.mapHom R f = b.hom ≫ Path.mapHom R g := congrArg Mon.Hom.hom h
  have hp := congrArg (fun t => (Cochain.ofHom t).comp (Path.primitive R D) (zero_add (-1))) hc
  rw [Cochain.ofHom_comp, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain, Cochain.comp_assoc_of_first_is_zero_cochain,
    Path.mapHom_primitive, Path.mapHom_primitive,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_first_is_zero_cochain] at hp
  exact hp

def primitiveLift : Cochain W.X (MonoidPullback.obj f g).X (-1) :=
  CochainPullback.lift f.hom g.hom (-1) (leftPrimitive R a) (rightPrimitive R b)
    (primitive_condition R f g a b h)

lemma primitiveLift_fst : (primitiveLift R f g a b h).comp
    (Cochain.ofHom (MonoidPullback.fst f g).hom) (add_zero (-1)) = leftPrimitive R a :=
  CochainPullback.lift_fst _ _ _ _ _ _

lemma primitiveLift_snd : (primitiveLift R f g a b h).comp
    (Cochain.ofHom (MonoidPullback.snd f g).hom) (add_zero (-1)) = rightPrimitive R b :=
  CochainPullback.lift_snd _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathPullback
