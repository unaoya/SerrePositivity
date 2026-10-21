module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativePathEndpoints
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathGradedZero
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
概要：同じ底の実二端点を、比較 cochain が零の斉次相対経路へ持ち上げる準備。
方針：元の二端点対と底の鎖写像の厳密な等式を、各次数の pullback に評価する。
規約：斉次経路を鎖写像とは扱わない。使われ方：相対二端点射の次数全射性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativePath
variable (R : Type u) [CommRing R] {C B : Mon (Complex R)} (p : C ⟶ B)

def pairHom : (endpoints R p).X ⟶ C.X ⊞ C.X :=
  biprod.lift (endpointsSource R p).hom (endpointsTarget R p).hom

lemma pairHom_fst : pairHom R p ≫ biprod.fst = (endpointsSource R p).hom :=
  biprod.lift_fst _ _

lemma pairHom_snd : pairHom R p ≫ biprod.snd = (endpointsTarget R p).hom :=
  biprod.lift_snd _ _

def baseHom : (endpoints R p).X ⟶ B.X := (endpointsSource R p).hom ≫ p.hom

lemma pairHom_base : pairHom R p ≫ biprod.map p.hom p.hom =
    baseHom R p ≫ biprod.lift (𝟙 B.X) (𝟙 B.X) := by
  dsimp only [pairHom, baseHom]
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.map_fst, ← Category.assoc, biprod.lift_fst,
      Category.assoc, biprod.lift_fst, Category.comp_id]
  · rw [Category.assoc, biprod.map_snd, ← Category.assoc, biprod.lift_snd,
      Category.assoc, biprod.lift_snd, Category.comp_id]
    exact (congrArg Mon.Hom.hom (endpoints_condition R p)).symm

lemma pairHom_zero_comm (n : ℤ) :
    ((pairHom R p).f n ≫ Path.gradedZero R C n) ≫ (Path.map R p).hom.f n =
      (baseHom R p).f n ≫ (Path.diagonal R B).hom.f n := by
  rw [Category.assoc, Path.gradedZero_map, ← Category.assoc, ← HomologicalComplex.comp_f,
    pairHom_base, HomologicalComplex.comp_f, Category.assoc, Path.gradedZero_diagonal]

lemma gradedPullback (n : ℤ) :
    IsPullback ((inclusion R p).hom.f n) ((projection R p).hom.f n)
      ((Path.map R p).hom.f n) ((Path.diagonal R B).hom.f n) :=
  Functor.map_isPullback (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) n)
    (IsPullback.of_hasPullback (Path.map R p).hom (Path.diagonal R B).hom)

lemma gradedEndpointsPullback (n : ℤ) :
    IsPullback ((endpointsSource R p).hom.f n) ((endpointsTarget R p).hom.f n)
      (p.hom.f n) (p.hom.f n) :=
  Functor.map_isPullback (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) n)
    (IsPullback.of_hasPullback p.hom p.hom)

def gradedZeroLift (n : ℤ) : (endpoints R p).X.X n ⟶ (algebra R p).X.X n :=
  (gradedPullback R p n).lift ((pairHom R p).f n ≫ Path.gradedZero R C n)
    ((baseHom R p).f n) (pairHom_zero_comm R p n)

lemma gradedZeroLift_inclusion (n : ℤ) :
    gradedZeroLift R p n ≫ (inclusion R p).hom.f n =
      (pairHom R p).f n ≫ Path.gradedZero R C n :=
  (gradedPullback R p n).lift_fst _ _ _

lemma gradedZeroLift_projection (n : ℤ) :
    gradedZeroLift R p n ≫ (projection R p).hom.f n = (baseHom R p).f n :=
  (gradedPullback R p n).lift_snd _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativePath
