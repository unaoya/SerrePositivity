module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWConstant
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplicialCategory

/-!
概要：標準Homの定数単体の最上位成分は、零次数で元の閉元、正次数で零。
方針：標準零単体の指定同値と既存の定数単体の成分則を使う。
規約：IS-W2 C05の既存構成の単位・評価則。
使われ方：HA 1.3.1.16、同じstrict図式のcoherent比較の高次成分。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] {x y : D}

/-- 標準Homの同じ定数単体は、正次数の最上位成分では零。 -/
theorem standardTopEval_constant_pos (z : (standardHomSpace (R := R) x y) _⦋0⦌)
    (m : ℕ) (hm : 0 < m) :
    standardTopEval x y m (PinchedHom.constant z m) = 0 := by
  let c := standardZeroEquiv (R := R) x y z
  have hz : standardZeroLift c = z := by
    apply standardZeroEval_injective x y
    apply Subtype.ext
    change (singleComponent (n := 0) Finset.univ 0 Finset.univ_nonempty (by simp) c.val).component
      Finset.univ 0 Finset.univ_nonempty (by simp) = c.val
    exact singleComponent_self (n := 0) _ _ _ _ c.val
  rw [← hz]
  change (standardConstant c m).val.component Finset.univ (-(m : ℤ))
    Finset.univ_nonempty (by simp) = 0
  apply standardConstant_component_zero
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

/-- 標準Homの定数零単体の最上位成分は、元の指定零単体の評価。 -/
theorem standardTopEval_constant_zero (z : (standardHomSpace (R := R) x y) _⦋0⦌) :
    standardTopEval x y 0 (PinchedHom.constant z 0) =
      (standardZeroEquiv (R := R) x y z).val := by
  have hc : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    change (_ : Fin 1) = (_ : Fin 1)
    exact Subsingleton.elim _ _
  simp only [PinchedHom.constant, hc, op_id]
  rw [(standardHomSpace (R := R) x y).map_id]
  rfl

/-- 同じ通常の閉零射の豊穣零単体の評価は、指定閉元そのもの。 -/
theorem standardZeroEquiv_homEquiv (x y : ClosedCategory R D) (f : x ⟶ y) :
    standardZeroEquiv (R := R) (D := D) x y
      (SimplicialCategory.homEquiv' x y f) = closedHomEquiv R D x y f := by
  change (standardZeroEquiv (R := R) (D := D) x y)
    ((standardHomSpace (R := R) (D := D) x y).unitHomEquiv
      ((standardHomSpace (R := R) (D := D) x y).unitHomEquiv.symm
        (closedStandardVertexEquiv (R := R) (D := D) x y f))) = _
  rw [Equiv.apply_symm_apply]
  exact (standardZeroEquiv (R := R) (D := D) x y).apply_symm_apply _

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
