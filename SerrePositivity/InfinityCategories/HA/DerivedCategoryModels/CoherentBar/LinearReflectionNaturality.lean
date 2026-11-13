module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LinearReflectionData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveOppositeReindex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedLinearChainMap
/-!
概要：線形座標の反転は、反転した全添字写像と厳密に可換である。
方針：部分集合上の単射分岐では反転像、非単射分岐では零成分を比較する。
規約：面・退化に加えて任意の単調写像を含む。
使われ方：左右 pinched Hom 比較を実単体写像として組み立てる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {C : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] {x y : C}

private lemma component_eq_of_set_eq {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n)
    {J K : Finset (Fin (n + 1))} {k : ℤ} {hJ : J.Nonempty} {hK : K.Nonempty}
    {hkJ : k = 1 - (J.card : ℤ)} {hkK : k = 1 - (K.card : ℤ)} (h : J = K) :
    f.component J k hJ hkJ = f.component K k hK hkK := by
  cases h
  rfl

lemma dgCoherentBarLinearReflectionData_pullback {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseOrderHom α) f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionData f) := by
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionData
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseOrderHom α) f)).component J k hJ hk =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionData f)).component J k hJ hk
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionData_component]
  by_cases hi : Set.InjOn α (J : Set (Fin (m + 1)))
  · have hiRev : Set.InjOn (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseOrderHom α) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse J : Set (Fin (m + 1))) := by
      apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseOrderHom_injOn_iff α (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse J)).mpr
      simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_reverse] using hi
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ hiRev,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ hi,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionData_component,
      Finset.card_image_of_injOn hi]
    congr 1
    exact component_eq_of_set_eq f (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverse_image α J).symm
  · have hiRev : ¬ Set.InjOn (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseOrderHom α) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse J : Set (Fin (m + 1))) := by
      intro h
      apply hi
      simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_reverse] using
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseOrderHom_injOn_iff α (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse J)).mp h
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_not_inj _ _ _ _ _ _ hiRev,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_not_inj _ _ _ _ _ _ hi, smul_zero]

lemma dgCoherentBarLinearReflectionSimplex_involution {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x y n) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionSimplex (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionSimplex f) = f := by
  apply Subtype.ext
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionData_involution f.val

lemma dgCoherentBarLinearReflectionSimplex_pullback {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x y n) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex.pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseOrderHom α) f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex.pullback α (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionSimplex f) := by
  apply Subtype.ext
  exact dgCoherentBarLinearReflectionData_pullback α f.val

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
