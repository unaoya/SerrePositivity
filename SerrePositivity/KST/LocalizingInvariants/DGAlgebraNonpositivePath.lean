module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveCoverLift
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveCoverSurjective
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathFunctor

/-!
概要：非正次数代数の実経路と両評価を、全て非正次数の代数として供給する。
方針：元の Path の connective cover を取り、実射の一意な持ち上げと閉元の充填を使う。
規約：両評価は次数全射準同型で、元の指定経路を保つ。使われ方：class 図式の底変更。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.NonpositivePath
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]

def algebra : Mon (Complex R) := connectiveCover R (Path.algebra R B)

omit [B.X.IsStrictlyLE 0] in
lemma nonpositive : (algebra R B).X.IsStrictlyLE 0 := coverComplex_nonpositive R _

def source : algebra R B ⟶ B := connectiveCoverInclusion R (Path.algebra R B) ≫ Path.source R B

def target : algebra R B ⟶ B := connectiveCoverInclusion R (Path.algebra R B) ≫ Path.target R B

lemma source_surjective (n : ℤ) : Function.Surjective ((source R B).hom.f n) :=
  connectiveCoverInclusion_comp_surjective R (Path.source R B)
    (Path.source_surjective R B) (Path.source_quasiIso R B) n

lemma target_surjective (n : ℤ) : Function.Surjective ((target R B).hom.f n) :=
  connectiveCoverInclusion_comp_surjective R (Path.target R B)
    (Path.target_surjective R B) (Path.target_quasiIso R B) n

lemma source_quasiIso : QuasiIso (source R B).hom :=
  connectiveCoverInclusion_comp_quasiIso R (Path.source R B) (Path.source_quasiIso R B)

lemma target_quasiIso : QuasiIso (target R B).hom :=
  connectiveCoverInclusion_comp_quasiIso R (Path.target R B) (Path.target_quasiIso R B)

def diagonal : B ⟶ algebra R B := connectiveCoverLift R (Path.diagonal R B)

lemma diagonal_source : diagonal R B ≫ source R B = 𝟙 B := by
  rw [diagonal, source, ← Category.assoc, connectiveCoverLift_inclusion, Path.diagonal_source]

lemma diagonal_target : diagonal R B ≫ target R B = 𝟙 B := by
  rw [diagonal, target, ← Category.assoc, connectiveCoverLift_inclusion, Path.diagonal_target]

variable {B} {A : Mon (Complex R)} [A.X.IsStrictlyLE 0] {f g : A ⟶ B}

def lift (w : Path.Witness R f g) : A ⟶ algebra R B := connectiveCoverLift R w.hom

omit [B.X.IsStrictlyLE 0] in
lemma lift_inclusion (w : Path.Witness R f g) :
    lift R w ≫ connectiveCoverInclusion R (Path.algebra R B) = w.hom :=
  connectiveCoverLift_inclusion R w.hom

lemma lift_source (w : Path.Witness R f g) : lift R w ≫ source R B = f := by
  rw [source, ← Category.assoc, lift_inclusion]
  exact w.source_eq

lemma lift_target (w : Path.Witness R f g) : lift R w ≫ target R B = g := by
  rw [target, ← Category.assoc, lift_inclusion]
  exact w.target_eq

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.NonpositivePath
