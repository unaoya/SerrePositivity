module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathPullbackCoordinates
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathPrimitiveBoundary

/-!
概要：pullback に持ち上げた比較 cochain は、元の両端差と正しい境界式を満たす。
方針：元の二射影の共同単射性と、各経路の実境界式へ帰着する。
規約：同じ源・標的 lift を使用。使われ方：実 pullback の経路への鎖写像。
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

lemma primitiveLift_boundary : δ (-1) 0 (primitiveLift R f g a b h) +
    Cochain.ofHom ((sourceLift R f g a b h).hom - (targetLift R f g a b h).hom) = 0 := by
  apply CochainPullback.hom_ext f.hom g.hom 0
  · change (δ (-1) 0 (primitiveLift R f g a b h) +
      Cochain.ofHom ((sourceLift R f g a b h).hom - (targetLift R f g a b h).hom)).comp
        (Cochain.ofHom (MonoidPullback.fst f g).hom) _ = _
    rw [Cochain.add_comp, Cochain.zero_comp, ← δ_comp_ofHom, primitiveLift_fst,
      ← Cochain.ofHom_comp, Preadditive.sub_comp]
    have hs : (sourceLift R f g a b h).hom ≫ (MonoidPullback.fst f g).hom =
        a.hom ≫ (Path.source R A).hom := congrArg Mon.Hom.hom (MonoidPullback.lift_fst _ _ _ _ _)
    have ht : (targetLift R f g a b h).hom ≫ (MonoidPullback.fst f g).hom =
        a.hom ≫ (Path.target R A).hom := congrArg Mon.Hom.hom (MonoidPullback.lift_fst _ _ _ _ _)
    rw [hs, ht]
    exact Path.primitive_precompose_boundary R A a.hom
  · change (δ (-1) 0 (primitiveLift R f g a b h) +
      Cochain.ofHom ((sourceLift R f g a b h).hom - (targetLift R f g a b h).hom)).comp
        (Cochain.ofHom (MonoidPullback.snd f g).hom) _ = _
    rw [Cochain.add_comp, Cochain.zero_comp, ← δ_comp_ofHom, primitiveLift_snd,
      ← Cochain.ofHom_comp, Preadditive.sub_comp]
    have hs : (sourceLift R f g a b h).hom ≫ (MonoidPullback.snd f g).hom =
        b.hom ≫ (Path.source R B).hom := congrArg Mon.Hom.hom (MonoidPullback.lift_snd _ _ _ _ _)
    have ht : (targetLift R f g a b h).hom ≫ (MonoidPullback.snd f g).hom =
        b.hom ≫ (Path.target R B).hom := congrArg Mon.Hom.hom (MonoidPullback.lift_snd _ _ _ _ _)
    rw [hs, ht]
    exact Path.primitive_precompose_boundary R B b.hom

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathPullback
