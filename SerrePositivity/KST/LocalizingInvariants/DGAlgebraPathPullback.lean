module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathPullbackChainLift
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathPullbackExt

/-!
概要：実経路関手は元の代数 pullback を、実 pullback の経路錐へ移す。
方針：比較 cochain を保つ鎖写像の単位・積保存を、二つの経路射影で検証する。
規約：元の二射影と普遍 lift を保持。使われ方：相対経路の底変更。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathPullback
variable (R : Type u) [CommRing R] {A B D W : Mon (Complex R)} (f : A ⟶ D) (g : B ⟶ D)
  (a : W ⟶ Path.algebra R A) (b : W ⟶ Path.algebra R B)
  (h : a ≫ Path.map R f = b ≫ Path.map R g)

lemma chainLift_one : η[W.X] ≫ chainLift R f g a b h =
    η[(Path.algebra R (MonoidPullback.obj f g)).X] := by
  apply chain_ext R f g
  · rw [Category.assoc, chainLift_fst]
    exact (IsMonHom.one_hom a.hom).trans
      (IsMonHom.one_hom (Path.map R (MonoidPullback.fst f g)).hom).symm
  · rw [Category.assoc, chainLift_snd]
    exact (IsMonHom.one_hom b.hom).trans
      (IsMonHom.one_hom (Path.map R (MonoidPullback.snd f g)).hom).symm

lemma chainLift_mul : μ[W.X] ≫ chainLift R f g a b h =
    (chainLift R f g a b h ⊗ₘ chainLift R f g a b h) ≫
      μ[(Path.algebra R (MonoidPullback.obj f g)).X] := by
  apply chain_ext R f g
  · rw [Category.assoc, chainLift_fst, Category.assoc]
    change μ[W.X] ≫ a.hom = _ ≫ μ[(Path.algebra R (MonoidPullback.obj f g)).X] ≫
      (Path.map R (MonoidPullback.fst f g)).hom
    rw [IsMonHom.mul_hom (Path.map R (MonoidPullback.fst f g)).hom,
      ← Category.assoc, tensorHom_comp_tensorHom]
    have hc : chainLift R f g a b h ≫ (Path.map R (MonoidPullback.fst f g)).hom = a.hom :=
      chainLift_fst R f g a b h
    rw [hc]
    exact IsMonHom.mul_hom a.hom
  · rw [Category.assoc, chainLift_snd, Category.assoc]
    change μ[W.X] ≫ b.hom = _ ≫ μ[(Path.algebra R (MonoidPullback.obj f g)).X] ≫
      (Path.map R (MonoidPullback.snd f g)).hom
    rw [IsMonHom.mul_hom (Path.map R (MonoidPullback.snd f g)).hom,
      ← Category.assoc, tensorHom_comp_tensorHom]
    have hc : chainLift R f g a b h ≫ (Path.map R (MonoidPullback.snd f g)).hom = b.hom :=
      chainLift_snd R f g a b h
    rw [hc]
    exact IsMonHom.mul_hom b.hom

def lift : W ⟶ Path.algebra R (MonoidPullback.obj f g) :=
  Mon.Hom.mk' (chainLift R f g a b h) (chainLift_one R f g a b h) (chainLift_mul R f g a b h)

lemma lift_fst : lift R f g a b h ≫ Path.map R (MonoidPullback.fst f g) = a := by
  apply Mon.Hom.ext
  exact chainLift_fst R f g a b h

lemma lift_snd : lift R f g a b h ≫ Path.map R (MonoidPullback.snd f g) = b := by
  apply Mon.Hom.ext
  exact chainLift_snd R f g a b h

lemma condition : Path.map R (MonoidPullback.fst f g) ≫ Path.map R f =
    Path.map R (MonoidPullback.snd f g) ≫ Path.map R g := by
  rw [← Path.map_comp, ← Path.map_comp, MonoidPullback.condition]

def cone : PullbackCone (Path.map R f) (Path.map R g) := PullbackCone.mk
  (Path.map R (MonoidPullback.fst f g)) (Path.map R (MonoidPullback.snd f g)) (condition R f g)

def isLimit : IsLimit (cone R f g) := PullbackCone.IsLimit.mk (condition R f g)
  (fun s => lift R f g s.fst s.snd s.condition)
  (fun s => lift_fst R f g s.fst s.snd s.condition)
  (fun s => lift_snd R f g s.fst s.snd s.condition)
  (fun s m hf hg => by
    apply Mon.Hom.ext
    apply chain_ext R f g
    · exact (congrArg Mon.Hom.hom hf).trans
        (congrArg Mon.Hom.hom (lift_fst R f g s.fst s.snd s.condition)).symm
    · exact (congrArg Mon.Hom.hom hg).trans
        (congrArg Mon.Hom.hom (lift_snd R f g s.fst s.snd s.condition)).symm)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathPullback
