module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativePathSurjectiveSource
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativePathWitnessLift

/-!
概要：同じ底の上の接続可能な二経路の実代数と、底を保つ両端評価を構成する。
方針：相対 target と source の実 pullback を使い、最初の評価の全射準同型性を示す。
規約：底射の準同型性は要求しない。使われ方：底を固定した cell 経路合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativeComposedPath
variable (R : Type u) [CommRing R] {C B : Mon (Complex R)} (p : C ⟶ B)

def algebra : Mon (Complex R) :=
  MonoidPullback.obj (RelativePath.target R p) (RelativePath.source R p)

def first : algebra R p ⟶ RelativePath.algebra R p :=
  MonoidPullback.fst (RelativePath.target R p) (RelativePath.source R p)

def second : algebra R p ⟶ RelativePath.algebra R p :=
  MonoidPullback.snd (RelativePath.target R p) (RelativePath.source R p)

def source : algebra R p ⟶ C := first R p ≫ RelativePath.source R p

def target : algebra R p ⟶ C := second R p ≫ RelativePath.target R p

lemma condition : first R p ≫ RelativePath.target R p =
    second R p ≫ RelativePath.source R p := MonoidPullback.condition _ _

lemma target_base : target R p ≫ p = source R p ≫ p := by
  rw [target, Category.assoc, RelativePath.target_projection,
    ← RelativePath.source_projection, ← Category.assoc, ← condition,
    Category.assoc, RelativePath.target_projection, ← RelativePath.source_projection,
    ← Category.assoc]
  rfl

def diagonal : C ⟶ algebra R p :=
  MonoidPullback.lift (RelativePath.target R p) (RelativePath.source R p)
    (RelativePath.diagonal R p) (RelativePath.diagonal R p)
    ((RelativePath.diagonal_target R p).trans (RelativePath.diagonal_source R p).symm)

lemma diagonal_source : diagonal R p ≫ source R p = 𝟙 C := by
  rw [diagonal, source, first, ← Category.assoc, MonoidPullback.lift_fst,
    RelativePath.diagonal_source]

lemma diagonal_target : diagonal R p ≫ target R p = 𝟙 C := by
  rw [diagonal, target, second, ← Category.assoc, MonoidPullback.lift_snd,
    RelativePath.diagonal_target]

lemma sourceEvaluation_epi : Epi (RelativePath.source R p).hom :=
  epi_of_epi_fac (congrArg Mon.Hom.hom (RelativePath.diagonal_source R p))

lemma source_surjective (n : ℤ) : Function.Surjective ((source R p).hom.f n) := by
  have := sourceEvaluation_epi R p
  exact ((ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi ((RelativePath.source R p).hom.f n))).comp
    (cochainPullback_fst_surjective (RelativePath.target R p).hom (RelativePath.source R p).hom n)

lemma source_quasiIso (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n)) :
    QuasiIso (source R p).hom := by
  have := sourceEvaluation_epi R p
  change QuasiIso ((MonoidPullback.fst (RelativePath.target R p) (RelativePath.source R p)).hom ≫
    (RelativePath.source R p).hom)
  exact quasiIso_comp _ _
    (hφ := cochainPullback_fst_quasiIso (RelativePath.target R p).hom (RelativePath.source R p).hom
      (RelativePath.source_quasiIso_of_surjective R p hs))
    (hφ' := RelativePath.source_quasiIso_of_surjective R p hs)

variable {W : Mon (Complex R)} {f g h : W ⟶ C}
  (v : Path.Witness R f g) (w : Path.Witness R g h)
  (hv : v.hom ≫ Path.map R p = (f ≫ p) ≫ Path.diagonal R B)
  (hw : w.hom ≫ Path.map R p = (g ≫ p) ≫ Path.diagonal R B)

def lift : W ⟶ algebra R p :=
  MonoidPullback.lift (RelativePath.target R p) (RelativePath.source R p)
    (RelativePath.witnessLift R p v hv) (RelativePath.witnessLift R p w hw)
    ((RelativePath.witnessLift_target R p v hv).trans
      (RelativePath.witnessLift_source R p w hw).symm)

lemma lift_source : lift R p v w hv hw ≫ source R p = f := by
  rw [lift, source, first, ← Category.assoc, MonoidPullback.lift_fst,
    RelativePath.witnessLift_source]

lemma lift_target : lift R p v w hv hw ≫ target R p = h := by
  rw [lift, target, second, ← Category.assoc, MonoidPullback.lift_snd,
    RelativePath.witnessLift_target]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativeComposedPath
