module
public import SerrePositivity.DifferentialGraded.Tensor.Fubini
public import SerrePositivity.DifferentialGraded.Tensor.Semifree
public import SerrePositivity.DifferentialGraded.Tensor.ProjectiveKFlat
public import SerrePositivity.DifferentialGraded.Bimodule.Evaluation
public import SerrePositivity.DifferentialGraded.Bimodule.Identity

/-! # 右制限の相対K-flat性とbimodule合成による保存 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 各左対象での右B加群が相対K-flatである条件。A上のobjectwise K-flat性とは別。 -/
def rightRelativeKFlat (P : Bimodule A B C) : Prop :=
  ∀ c : C, moduleRelativeKFlat A B (P.rightAt c)

lemma rightRelativeKFlat_of_iso {P Q : BimoduleCategory A B C} (e : P ≅ Q)
    (h : rightRelativeKFlat A B C (BimoduleCategory.underlying A B C Q)) :
    rightRelativeKFlat A B C (BimoduleCategory.underlying A B C P) := by
  intro c
  exact moduleRelativeKFlat_of_iso A B ((BimoduleCategory.evaluation A B C c).mapIso e) (h c)

lemma rightRelativeKFlat_of_retract {P Q : BimoduleCategory A B C} (e : Retract P Q)
    (h : rightRelativeKFlat A B C (BimoduleCategory.underlying A B C Q)) :
    rightRelativeKFlat A B C (BimoduleCategory.underlying A B C P) := by
  intro c
  exact moduleRelativeKFlat_of_retract A B (e.map (BimoduleCategory.evaluation A B C c)) (h c)

/-- 片側の各制限にsemifree性の証拠がある場合の十分条件。 -/
lemma rightRelativeKFlat_of_rightAt_semifree (P : Bimodule A B C)
    (h : ∀ c, moduleSemifree A B (ForgetEnrichment.of (Complex A) (P.rightAt c))) :
    rightRelativeKFlat A B C P := by
  intro c
  exact moduleSemifree_relativeKFlat A B (h c)

/-- 片側の各制限の全Hom射影性も相対K-flat性を与える。 -/
lemma rightRelativeKFlat_of_rightAt_projective (P : Bimodule A B C)
    (h : ∀ c, moduleHomotopicallyProjective A B
      (ForgetEnrichment.of (Complex A) (P.rightAt c))) : rightRelativeKFlat A B C P := by
  intro c
  exact moduleHomotopicallyProjective_relativeKFlat A B (h c)

lemma diagonal_rightRelativeKFlat : rightRelativeKFlat A B B (diagonal A B) :=
  fun b => representable_relativeKFlat A B b

variable [Small.{u} C] (E : Type z) [DGCategory A E]

/-- Fubiniにより、右制限が相対K-flatな二つのbimoduleの合成も同じ条件を満たす。 -/
lemma rightRelativeKFlat_compose (P : Bimodule A B C) (Q : Bimodule A C E)
    (hP : rightRelativeKFlat A B C P) (hQ : rightRelativeKFlat A C E Q) :
    rightRelativeKFlat A B E (BimoduleTensor.compose A B C E P Q) := by
  intro e N hN
  have hL : leftModuleAcyclic A C (BalancedTensor.Fubini.leftModule A B C P N) :=
    fun c => hP c N hN
  have h := hQ e (BalancedTensor.Fubini.leftModule A B C P N) hL
  exact cochainAcyclic_of_iso h (BalancedTensor.Fubini.iso A B C P (Q.rightAt e) N)

end SerrePositivity.DifferentialGraded.Bimodule
