module
public import SerrePositivity.KST.SConstruction.SerreIntervalEndpointDuals

/-! # 元の区間生成元の指定値から次数線形射を復元
概要：元の二端点・辺の指定次数での任意の値から、元の区間次数加群の線形射を作る。
方針：元の双対座標と元の A の単位からの射を合成し、次数で場合分けする。
規約：鎖射の微分条件はまだ課さない。使われ方：実 tensor の全生成元値の線形復元。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の二端点の値から、元の次数零の線形射を復元する。 -/
def serreIntervalDegreeZeroLift (V : ModuleCat.{u} A) (z₀ z₁ : V) :
    (serreInterval A).X 0 ⟶ V :=
  serreIntervalZeroCoordinate A ≫ moduleElementMap A V z₀ +
    serreIntervalBoundaryCoordinate A ≫ moduleElementMap A V z₁

/-- 元の次数零の復元は、元の零端点に指定した値を回収する。 -/
lemma serreIntervalDegreeZeroLift_zero (V : ModuleCat.{u} A) (z₀ z₁ : V) :
    serreIntervalDegreeZeroLift A V z₀ z₁ (cycleFromUnit _ (serreIntervalZero A)).val = z₀ := by
  change serreIntervalZeroCoordinate A (cycleFromUnit _ (serreIntervalZero A)).val • z₀ +
    serreIntervalBoundaryCoordinate A (cycleFromUnit _ (serreIntervalZero A)).val • z₁ = z₀
  rw [serreIntervalZeroCoordinate_zero, serreIntervalBoundaryCoordinate_zero,
    one_smul, zero_smul, add_zero]

/-- 元の次数零の復元は、元の一端点に指定した値を回収する。 -/
lemma serreIntervalDegreeZeroLift_one (V : ModuleCat.{u} A) (z₀ z₁ : V) :
    serreIntervalDegreeZeroLift A V z₀ z₁ (cycleFromUnit _ (serreIntervalOne A)).val = z₁ := by
  change serreIntervalZeroCoordinate A (cycleFromUnit _ (serreIntervalOne A)).val • z₀ +
    serreIntervalBoundaryCoordinate A (cycleFromUnit _ (serreIntervalOne A)).val • z₁ = z₁
  rw [serreIntervalZeroCoordinate_one, serreIntervalBoundaryCoordinate_one,
    zero_smul, one_smul, zero_add]

/-- 元の辺の値から、元の次数 −1 の線形射を復元する。 -/
def serreIntervalDegreeEdgeLift (V : ModuleCat.{u} A) (e : V) :
    (serreInterval A).X (-1) ⟶ V := serreIntervalEdgeCoordinate A ≫ moduleElementMap A V e

/-- 元の次数 −1 の復元は、元の辺に指定した値を回収する。 -/
lemma serreIntervalDegreeEdgeLift_edge (V : ModuleCat.{u} A) (e : V) :
    serreIntervalDegreeEdgeLift A V e (serreIntervalEdge A) = e := by
  change serreIntervalEdgeCoordinate A (serreIntervalEdge A) • e = e
  rw [serreIntervalEdgeCoordinate_edge, one_smul]

/-- 元の指定次数の全端点・辺生成元の値から、元の次数線形射を復元する。 -/
def serreIntervalDegreeLift (k : ℤ) (V : ModuleCat.{u} A)
    (v : ∀ i : Fin 3, serreIntervalGeneratorDegree i = k → V) : (serreInterval A).X k ⟶ V :=
  if h₀ : k = 0 then
    eqToHom (congrArg (fun d => (serreInterval A).X d) h₀) ≫
      serreIntervalDegreeZeroLift A V (v 0 h₀.symm) (v 1 h₀.symm)
  else if h₁ : k = -1 then
    eqToHom (congrArg (fun d => (serreInterval A).X d) h₁) ≫ serreIntervalDegreeEdgeLift A V
      (v 2 h₁.symm)
  else 0

/-- 元の次数線形射の復元は、元の全ての指定した生成元値を回収する。 -/
lemma serreIntervalDegreeLift_generator (k : ℤ) (V : ModuleCat.{u} A)
    (v : ∀ i : Fin 3, serreIntervalGeneratorDegree i = k → V)
    (i : Fin 3) (hi : serreIntervalGeneratorDegree i = k) :
    serreIntervalDegreeLift A k V v
        (eqToHom (congrArg (fun d => (serreInterval A).X d) hi) (serreIntervalGenerator A i)) =
      v i hi := by
  fin_cases i
  · subst k
    change serreIntervalDegreeLift A 0 V v (cycleFromUnit _ (serreIntervalZero A)).val = v 0 rfl
    unfold serreIntervalDegreeLift
    erw [dite_eq_left rfl]
    simpa only [eqToHom_refl, Category.id_comp] using
      serreIntervalDegreeZeroLift_zero A V (v 0 rfl) (v 1 rfl)
  · subst k
    change serreIntervalDegreeLift A 0 V v (cycleFromUnit _ (serreIntervalOne A)).val = v 1 rfl
    unfold serreIntervalDegreeLift
    erw [dite_eq_left rfl]
    simpa only [eqToHom_refl, Category.id_comp] using
      serreIntervalDegreeZeroLift_one A V (v 0 rfl) (v 1 rfl)
  · subst k
    change serreIntervalDegreeLift A (-1) V v (serreIntervalEdge A) = v 2 rfl
    unfold serreIntervalDegreeLift
    erw [dite_eq_right (show (-1 : ℤ) ≠ 0 by decide), dite_eq_left rfl]
    simpa only [eqToHom_refl, Category.id_comp] using
      serreIntervalDegreeEdgeLift_edge A V (v 2 rfl)

end SerrePositivity.KST.SConstruction
