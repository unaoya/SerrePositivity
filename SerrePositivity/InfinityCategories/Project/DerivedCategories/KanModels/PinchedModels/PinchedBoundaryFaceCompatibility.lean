module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedHomChainMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedBoundaryData

/-! # pinched 全境界と Hom 鎖写像の整合性

概要：相対境界の可換性から回収した全真部分集合の像を同定する。
方針：部分集合を含む面を選び、線形表示の自然性を用いる。
規約：全境界を実際の単体集合の射として扱う。使われ方：β3 の相対充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D E : Type v}
variable [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] {x y : D} {x' y' : E}

/-- 全ての面が等しい線形データは真部分集合の成分が等しい。 -/
lemma pinchedLinearData_proper_eq_of_faces {n : ℕ} (f g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y (n + 1))
    (hf : ∀ j : Fin (n + 2),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom f =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom g)
    (I : Finset (Fin (n + 2))) (k : ℤ) (hI : I.Nonempty) (hk : k = 1 - (I.card : ℤ))
    (hne : I ≠ Finset.univ) : f.component I k hI hk = g.component I k hI hk := by
  obtain ⟨j, hj⟩ : ∃ j, j ∉ I := by
    simpa only [ne_eq, Finset.eq_univ_iff_forall, not_forall] using hne
  let J := I.preimage j.succAbove j.succAboveOrderEmb.injective.injOn
  have hcard : J.card = I.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_preimage I j hj
  have hJ : J.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact hI.card_pos)
  have hImage : J.image j.succAboveOrderEmb.toOrderHom = I := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.image_preimage I j hj
  have h := congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n =>
    z.component J k hJ (by rw [hcard]; exact hk)) (hf j)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn] at h
  simpa only [hImage] using h

/-- 相対全境界から回収した既知成分は全真部分集合で目標単体へ写る。 -/
lemma pinchedBoundaryKnownData_map_proper
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject A D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject A E x' y') {n : ℕ}
    (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A E x' y') _⦋n + 1⦌)
    (hb : b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap φ = (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm t)
    (I : Finset (Fin (n + 2))) (k : ℤ) (hI : I.Nonempty) (hk : k = 1 - (I.card : ℤ))
    (hne : I ≠ Finset.univ) :
    φ.f k ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryKnownData b).component I k hI hk) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex t).val.component I k hI hk := by
  apply pinchedLinearData_proper_eq_of_faces (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryKnownData b))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex t).val ?_ I k hI hk hne
  intro j
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap_pullback, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryKnownData_pullback_face]
  have h := congrArg (fun z => SSet.yonedaEquiv (SSet.boundary.ι j ≫ z)) hb
  rw [← Category.assoc, SSet.yonedaEquiv_comp, ← Category.assoc,
    SSet.boundary.ι_ι, SSet.stdSimplex.δ_comp_yonedaEquiv_symm] at h
  simp only [Equiv.apply_symm_apply] at h
  have hl := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex φ
    (SSet.yonedaEquiv (SSet.boundary.ι j ≫ b))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (t.pullback (SimplexCategory.δ j)) at hl
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_pullback] at hl
  exact congrArg Subtype.val hl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
