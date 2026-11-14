module

public import SerrePositivity.AlgebraicGeometry.CoefficientSubalgebraDiagram
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
概要：指定係数環の有限生成部分代数の Spec と、元の Spec の実際の極限。
方針：包含による環の filtered colimit を、右随伴 Spec の極限保存で移す。
規約：遷移の忠実平坦性は仮定しない。
使われ方：G2 の有限表示の模型と重なりの射の共通有限段。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v
variable (k : Type v) (R : Type u) [CommRing k] [CommRing R] [Algebra k R]

/-- 実際の有限生成係数部分代数の Spec の逆系。 -/
def coefficientSpecDiagram : (Finset R)ᵒᵖ ⥤ Scheme.{u} :=
  (coefficientSubalgebraDiagram k R).op ⋙ Scheme.Spec

/-- 元の Spec R と同じ係数包含からなる cone。 -/
def coefficientSpecCone : Cone (coefficientSpecDiagram k R) :=
  Scheme.Spec.mapCone (coefficientSubalgebraCocone k R).op

/-- 元の Spec R は有限生成係数部分代数の Spec の実際の逆極限。 -/
def coefficientSpecConeIsLimit : IsLimit (coefficientSpecCone k R) :=
  isLimitOfPreserves Scheme.Spec (IsColimit.op (coefficientSubalgebraCoconeIsColimit k R))

/-- 係数部分代数の包含から来る実際の射影。 -/
theorem coefficientSpecCone_projection (s : Finset R) :
    (coefficientSpecCone k R).π.app (.op s) =
      Spec.map (CommRingCat.ofHom (Algebra.adjoin k (s : Set R)).val.toRingHom) := rfl

end SerrePositivity.AlgebraicGeometry
