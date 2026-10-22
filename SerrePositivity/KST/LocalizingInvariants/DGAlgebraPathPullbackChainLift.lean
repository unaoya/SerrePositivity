module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathPullbackBoundary

/-!
概要：一致する実経路から、元の pullback の実経路複体への鎖写像を構成する。
方針：持ち上げた両端と比較 cochain の境界式を、元の mapping cocone lift へ渡す。
規約：両射影の経路を回収。使われ方：経路関手による実 pullback 保存。
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

lemma pair_difference : biprod.lift (sourceLift R f g a b h).hom (targetLift R f g a b h).hom ≫
    Path.difference R (MonoidPullback.obj f g) =
      (sourceLift R f g a b h).hom - (targetLift R f g a b h).hom := by
  rw [Path.difference_eq, Preadditive.comp_sub, biprod.lift_fst, biprod.lift_snd]

def chainLift : W.X ⟶ (Path.algebra R (MonoidPullback.obj f g)).X :=
  mappingCocone.lift (Path.difference R (MonoidPullback.obj f g))
    (biprod.lift (sourceLift R f g a b h).hom (targetLift R f g a b h).hom)
    (primitiveLift R f g a b h) (by rw [pair_difference]; exact primitiveLift_boundary R f g a b h)

lemma chainLift_source : chainLift R f g a b h ≫
    (Path.source R (MonoidPullback.obj f g)).hom = (sourceLift R f g a b h).hom := by
  change chainLift R f g a b h ≫
    (mappingCocone.fst (Path.difference R (MonoidPullback.obj f g)) ≫ biprod.fst) = _
  rw [← Category.assoc, chainLift, mappingCocone.lift_fst, biprod.lift_fst]

lemma chainLift_target : chainLift R f g a b h ≫
    (Path.target R (MonoidPullback.obj f g)).hom = (targetLift R f g a b h).hom := by
  change chainLift R f g a b h ≫
    (mappingCocone.fst (Path.difference R (MonoidPullback.obj f g)) ≫ biprod.snd) = _
  rw [← Category.assoc, chainLift, mappingCocone.lift_fst, biprod.lift_snd]

lemma chainLift_primitive : (Cochain.ofHom (chainLift R f g a b h)).comp
    (Path.primitive R (MonoidPullback.obj f g)) (zero_add (-1)) = primitiveLift R f g a b h := by
  apply Cochain.ext
  intro p q hpq
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  exact mappingCocone.lift_f_snd_v _ _ _ _ p q hpq

lemma chainLift_fst : chainLift R f g a b h ≫ Path.mapHom R (MonoidPullback.fst f g) = a.hom := by
  apply Path.chain_ext R A
  · rw [Category.assoc, Path.mapHom_source, ← Category.assoc, chainLift_source]
    exact congrArg Mon.Hom.hom (MonoidPullback.lift_fst _ _ _ _ _)
  · rw [Category.assoc, Path.mapHom_target, ← Category.assoc, chainLift_target]
    exact congrArg Mon.Hom.hom (MonoidPullback.lift_fst _ _ _ _ _)
  · rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
      Path.mapHom_primitive, ← Cochain.comp_assoc_of_first_is_zero_cochain,
      chainLift_primitive, primitiveLift_fst]
    rfl

lemma chainLift_snd : chainLift R f g a b h ≫ Path.mapHom R (MonoidPullback.snd f g) = b.hom := by
  apply Path.chain_ext R B
  · rw [Category.assoc, Path.mapHom_source, ← Category.assoc, chainLift_source]
    exact congrArg Mon.Hom.hom (MonoidPullback.lift_snd _ _ _ _ _)
  · rw [Category.assoc, Path.mapHom_target, ← Category.assoc, chainLift_target]
    exact congrArg Mon.Hom.hom (MonoidPullback.lift_snd _ _ _ _ _)
  · rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
      Path.mapHom_primitive, ← Cochain.comp_assoc_of_first_is_zero_cochain,
      chainLift_primitive, primitiveLift_snd]
    rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathPullback
