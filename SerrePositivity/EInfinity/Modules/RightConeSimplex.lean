module
public import SerrePositivity.EInfinity.Modules.RightConeTerminalTerm
public import SerrePositivity.EInfinity.Modules.RightConeFrontEquation

/-!
概要：指定 augmentation を持つ実加群の任意 dg 単体に、同じ終端を追加した実単体を作る。
方針：前面は元の HA、終端を含む集合は閉性と各内部項の相殺で全方程式を証明する。
規約：HA Construction 1.3.1.6・1.3.1.13、存在を追加仮定しない。使われ方：元の cone の二重 cone と全三角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleRightConeData_equation_last {n : ℕ}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n} {M : ModuleCategory A D}
    (η : ModuleSimplexAugmentation A D s M) (I : Finset (Fin (n + 2)))
    (hl : Fin.last (n + 1) ∈ I) : (moduleRightConeData A D η).Equation I := by
  intro a b k hI ha hb hk
  have hbl : b = Fin.last (n + 1) := hb.trans
    ((I.isGreatest_max' _).unique ⟨hl, fun _ _ => Fin.le_last _⟩)
  rw [moduleRightConeData_differential_last A D η I a b k hI ha hb hk hbl]
  symm
  apply Finset.sum_eq_zero
  intro j _
  by_cases hint : a < j.val ∧ j.val < b
  · simp only [dite_eq_left hint]
    exact moduleRightConeData_term_last A D η I a b k hI ha hb hk hbl j.val j.property
      hint.1 hint.2
  · simp only [dite_eq_right hint]

def moduleRightConeSimplex {n : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n} {M : ModuleCategory A D}
    (η : ModuleSimplexAugmentation A D s M) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) (n + 1) where
  toSimplexData := moduleRightConeData A D η
  equation I := by
    by_cases hl : Fin.last (n + 1) ∈ I
    · exact moduleRightConeData_equation_last A D η I hl
    · exact moduleRightConeData_equation_without_last A D η I hl

lemma moduleRightConeSimplex_data {n : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n} {M : ModuleCategory A D}
    (η : ModuleSimplexAugmentation A D s M) :
    (moduleRightConeSimplex A D η).toSimplexData = moduleRightConeData A D η := rfl

lemma moduleRightConeSimplex_front {n : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n} {M : ModuleCategory A D}
    (η : ModuleSimplexAugmentation A D s M) :
    (moduleRightConeSimplex A D η).pullback Fin.castSuccOrderEmb.toOrderHom = s := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_data]
  exact moduleRightConeData_front A D η

end SerrePositivity.EInfinity.Modules
