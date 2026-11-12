module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseRawMixedNaturality
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.EquationTransfer
/-!
概要：指定部分集合の方程式を、単射による制限の等号に沿って移送する。
方針：既存の成分・右辺の単射公式を使い、全単体方程式の仮定は要求しない。
規約：方程式を満たす必要があるのは指定集合だけ。
使われ方：全頂点で証明した逆構成の方程式を任意の混合部分集合へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial

lemma dgCoherentBarEquation_image_of_pullback {R : Type u} [CommRing R]
    {C : Type v} [DGCategory R C] {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n)
    (α : Fin (m + 1) →o Fin (n + 1)) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C m)
    (h : s.pullback α = t) (J : Finset (Fin (m + 1)))
    (he : t.Equation J) (hi : Set.InjOn α (J : Set (Fin (m + 1)))) :
    s.Equation (J.image α) := by
  intro a b k hI ha hb hk
  have hcard : (J.image α).card = J.card := Finset.card_image_of_injOn hi
  have hJ : 2 ≤ J.card := by omega
  have hkJ : k = 2 - (J.card : ℤ) := by rwa [hcard] at hk
  let a' := J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
  let b' := J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
  have ha' : α a' = a := by
    rw [ha]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min α.monotone (J.isLeast_min' _) _
  have hb' : α b' = b := by
    rw [hb]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max α.monotone (J.isGreatest_max' _) _
  have hh := he a' b' k hJ rfl rfl hkJ
  rw [← h, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullback_rhs_of_inj _ _ _ _ _ _ _ _ _ _ hi] at hh
  cases ha'
  cases hb'
  exact hh

variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

lemma dgCoherentBarInverseRawData_equation_univ {m n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f.val s).Equation Finset.univ := by
  intro a b k hJ ha hb hk
  have ha0 : a = 0 := ha.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min (n + m)).symm
  have hbl : b = Fin.last (n + m + 1) := hb.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max (n + m)).symm
  have hk0 : k = -((n + m : ℕ) : ℤ) := by
    simp only [Finset.card_univ, Fintype.card_fin] at hk
    omega
  cases ha0
  cases hbl
  cases hk0
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData_full_equation R D F hMC N f s

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
