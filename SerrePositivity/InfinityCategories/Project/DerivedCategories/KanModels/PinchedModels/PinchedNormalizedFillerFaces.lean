module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedNormalizedFiller

/-! # 正規化した差の充填の実際の面と最上位成分

概要：指定原始元で作った一段高い単体の零面は差であり、他の面は厳密に零となる。
方針：置換で保持した全真部分集合を余面へ引き戻し、実境界の指定面を回収する。
規約：符号付き原始元そのものを最上位に持つ。使われ方：prism への貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D}

/-- 正規化した充填の全ての線形面は、指定された差または零に一致。 -/
lemma PinchedTopComparison.normalizedFiller_pullback {n : ℕ}
    {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y (n + 1)} (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison s t) (j : Fin (n + 3)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex.pullback j.succAboveOrderEmb.toOrderHom c.normalizedFiller =
      if j = 0 then s - t else 0 := by
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom c.normalizedFiller.val = _
  have hr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedNormalizedBoundary_faceData (s - t) c.difference_proper_zero j
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryKnownData_pullback_face
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedNormalizedBoundary (s - t) c.difference_proper_zero) j
  rw [hr] at hp
  have ht : (if j = 0 then s - t else 0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y (n + 1)).val =
      if j = 0 then (s - t).val else 0 := by split_ifs <;> rfl
  rw [ht, ← hp]
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  let f := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryKnownData
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedNormalizedBoundary (s - t) c.difference_proper_zero)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom c.normalizedFiller.val).component
    J k hJ hk = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom f).component J k hJ hk
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedCompleteTopAtDegree_proper _ _ _ _ _ _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundary_image_ne_univ j J)

/-- 一段高い実 pinched 単体の零面は差、他の面は零。 -/
lemma PinchedTopComparison.normalizedFiller_face {n : ℕ}
    {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y (n + 1)} (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison s t) (j : Fin (n + 3)) :
    c.normalizedFiller.toPinched.pullback (SimplexCategory.δ j) =
      (if j = 0 then s - t else 0).toPinched := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x y (n + 1)).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (c.normalizedFiller.toPinched.pullback (SimplexCategory.δ j)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (if j = 0 then s - t else 0).toPinched
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_pullback, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched]
  exact c.normalizedFiller_pullback j

/-- 最上位成分は、零面の削除係数を掛けた指定原始元そのもの。 -/
lemma PinchedTopComparison.normalizedFiller_full {n : ℕ}
    {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y (n + 1)} (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison s t) :
    c.normalizedFiller.val.component Finset.univ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree (n + 1) - 1)
      Finset.univ_nonempty (by simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree]; omega) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSign (Finset.univ : Finset (Fin (n + 3))) 0 • c.primitive :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedCompleteTopAtDegree_full _ _ _ _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
