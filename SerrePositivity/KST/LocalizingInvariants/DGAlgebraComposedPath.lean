module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMappingPathProjection
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathFunctor

/-!
概要：二つの接続可能な実乗法的経路の代数と、元の端点を保つ実射を構成する。
方針：target と source の実 pullback を使い、最初の評価を全射準同型とする。
規約：経路を向き反転する代数射を仮定しない。使われ方：cell 上の経路合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.ComposedPath
variable (R : Type u) [CommRing R] (B : Mon (Complex R))

def algebra : Mon (Complex R) := MonoidPullback.obj (Path.target R B) (Path.source R B)

def source : algebra R B ⟶ B :=
  MonoidPullback.fst (Path.target R B) (Path.source R B) ≫ Path.source R B

def target : algebra R B ⟶ B :=
  MonoidPullback.snd (Path.target R B) (Path.source R B) ≫ Path.target R B

def diagonal : B ⟶ algebra R B :=
  MonoidPullback.lift (Path.target R B) (Path.source R B) (Path.diagonal R B)
    (Path.diagonal R B) ((Path.diagonal_target R B).trans (Path.diagonal_source R B).symm)

lemma diagonal_source : diagonal R B ≫ source R B = 𝟙 B := by
  rw [diagonal, source, ← Category.assoc, MonoidPullback.lift_fst, Path.diagonal_source]

lemma diagonal_target : diagonal R B ≫ target R B = 𝟙 B := by
  rw [diagonal, target, ← Category.assoc, MonoidPullback.lift_snd, Path.diagonal_target]

lemma source_surjective (n : ℤ) : Function.Surjective ((source R B).hom.f n) := by
  have := MappingPath.source_epi (B := B) R
  exact (Path.source_surjective R B n).comp
    (cochainPullback_fst_surjective (Path.target R B).hom (Path.source R B).hom n)

lemma source_quasiIso : QuasiIso (source R B).hom := by
  have := MappingPath.source_epi (B := B) R
  change QuasiIso ((MonoidPullback.fst (Path.target R B) (Path.source R B)).hom ≫
    (Path.source R B).hom)
  exact quasiIso_comp _ _
    (hφ := cochainPullback_fst_quasiIso (Path.target R B).hom (Path.source R B).hom
      (Path.source_quasiIso R B)) (hφ' := Path.source_quasiIso R B)

variable {B} {A : Mon (Complex R)} {f g h : A ⟶ B}

def lift (a : Path.Witness R f g) (b : Path.Witness R g h) : A ⟶ algebra R B :=
  MonoidPullback.lift _ _ a.hom b.hom (a.target_eq.trans b.source_eq.symm)

lemma lift_source (a : Path.Witness R f g) (b : Path.Witness R g h) :
    lift R a b ≫ source R B = f := by
  rw [lift, source, ← Category.assoc, MonoidPullback.lift_fst]
  exact a.source_eq

lemma lift_target (a : Path.Witness R f g) (b : Path.Witness R g h) :
    lift R a b ≫ target R B = h := by
  rw [lift, target, ← Category.assoc, MonoidPullback.lift_snd]
  exact b.target_eq

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.ComposedPath
