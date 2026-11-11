module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaPinchedPrismCutSecond

/-! 唯一の切断の右係数は、最小点を消した元 Hom の線形成分への比較 cochain の作用である。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)

lemma dgGluingCommaHomotopyComponent_smul_heq
    {X Y X' Y' : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F} {p q : ℤ}
    (hx : X = X') (hy : Y = Y') (hp : p = q)
    (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R X Y p) (b : _root_.SerrePositivity.DifferentialGraded.GradedHom R X' Y' q) (hab : HEq a b) (σ : ℤˣ) :
    HEq (σ • _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R C E F X Y p a)
      (σ • _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R C E F X' Y' q b) := by
  cases hx
  cases hy
  cases hp
  rw [eq_of_heq hab]

variable {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F} {n : ℕ}
  (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) X Y) _⦋n⦌)

lemma dgGluingCommaPinchedPrismRightCorrection_linear
    (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPrismRightCorrection R C E F s.val.toSimplexData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J)
        (Fin.last (n + 1)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast J _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.second J hJ).castSucc (Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨_, (Finset.mem_erase.mp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.second_mem_erase J hJ)).2, rfl⟩)) (Fin.castSucc_lt_last _))
      ((((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J).filter ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.second J hJ).castSucc < ·)).card : ℤ).negOnePow •
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R C E F X Y (k + 1)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component (J.erase (J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))) (k + 1)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hJ _ (J.min'_mem _))
            (by have := Finset.card_erase_add_one (J.min'_mem (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)); omega))) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPrismRightCorrection]
  apply dgGluingCommaHomotopyComponent_smul_heq
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.source_obj s _
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.target_obj s
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.right_withLast, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.right_second, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast]
    have := Finset.card_erase_add_one (J.min'_mem (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    omega
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.cutRight_second_heq_component s J hJ k hk

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
