module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeFamilyHomDifferential
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.ParameterSubsetLabels
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeParameterDegeneracies
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedLinear
/-!
概要：高次余錐族の部分単体の Hom を、既存の右 pinched Hom の線形成分族へまとめる。
方針：部分単体を昇順列挙し、次数 r に符号 (−1)^r を掛けて右模型の規約へ移す。
規約：ここでは成分族を定義し、線形単体方程式は後続で証明する。
使われ方：全写像空間の逆比較を既存の pinched 成分模型に接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F)
  (y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)) _⦋0⦌)

def dgCoherentBarCoconeSubsetParameterHom {n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y) _⦋n⦌) (J : Finset (Fin (n + 1)))
    (r : ℕ) (hc : J.card = r + 1) :
    GradedHom R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv R (RightModule R D) y) (-(r : ℤ)) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilyHom R D F hMC y
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y).map (SimplexCategory.mkHom (J.orderEmbOfFin hc).toOrderHom).op c)

def dgCoherentBarCoconeSubsetHom {n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y) _⦋n⦌) (J : Finset (Fin (n + 1)))
    (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    GradedHom R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv R (RightModule R D) y) k :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := R) (D := RightModule R D) rfl rfl
    (show -((J.card - 1 : ℕ) : ℤ) = k by have := Finset.card_pos.mpr hJ; omega)
    (((J.card - 1 : ℕ) : ℤ).negOnePow •
      dgCoherentBarCoconeSubsetParameterHom R D F hMC y c J (J.card - 1)
        (by have := Finset.card_pos.mpr hJ; omega))

def dgCoherentBarCoconeLinearData {n : ℕ} (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv R (RightModule R D) y) n :=
  fun i => dgCoherentBarCoconeSubsetHom R D F hMC y c i.val.1 i.val.2 i.property.1 i.property.2

lemma dgCoherentBarCoconeSubsetHom_heq {n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y) _⦋n⦌) (J : Finset (Fin (n + 1)))
    (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (r : ℕ) (hc : J.card = r + 1) :
    HEq (dgCoherentBarCoconeSubsetHom R D F hMC y c J k hJ hk)
      ((r : ℤ).negOnePow • dgCoherentBarCoconeSubsetParameterHom R D F hMC y c J r hc) := by
  have hr : J.card - 1 = r := by omega
  cases hr
  unfold dgCoherentBarCoconeSubsetHom
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq _ _ _ _

lemma dgCoherentBarCoconeFamilyHom_heq_of_index_eq {m n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y) _⦋m⦌) (c' : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y) _⦋n⦌)
    (h : (⟨m, c⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y)) = ⟨n, c'⟩) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilyHom R D F hMC y c)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilyHom R D F hMC y c') := by
  cases h
  rfl

lemma dgCoherentBarCoconeFamilyHom_degenerate
    (a : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegenerateIndex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilyHom R D F hMC y a.val.2 = 0 := by
  rcases a with ⟨⟨n, c⟩, hc⟩
  cases n with
  | zero => simp only [SSet.degenerate_zero, Set.mem_empty_iff_false] at hc
  | succ n =>
    rw [SSet.degenerate_eq_iUnion_range_σ] at hc
    obtain ⟨i, c, rfl⟩ := Set.mem_iUnion.mp hc
    exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilyHom_parameter_degeneracy R D F y hMC c i

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
