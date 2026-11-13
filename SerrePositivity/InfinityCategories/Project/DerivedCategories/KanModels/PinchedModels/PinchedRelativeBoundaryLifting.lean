module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedBoundaryFaceCompatibility
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedRelativeSimplexLifting

/-! # Hom 鎖写像に沿う pinched 写像空間の相対全境界充填

概要：実際の全境界と指定された目標単体を同時に持ち上げる。
方針：境界成分を回収し、最上位だけを相対原始元に置き換える。
規約：正次元の全境界を扱う。使われ方：β3 の局所充満忠実性。
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

/-- 正次元の相対境界は全ての面と目標単体を厳密に保って充填できる。 -/
lemma pinchedHomChainMap_relative_boundary_lift
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject A D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject A E x' y')
    (hs : ∀ i : ℤ, Function.Surjective (φ.f i)) (hq : QuasiIso φ) {n : ℕ}
    (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A E x' y') _⦋n + 1⦌)
    (hb : b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap φ = (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm t) :
    ∃ L : (Δ[n + 1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y,
      (∂Δ[n + 1]).ι ≫ L = b ∧ L ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap φ = SSet.yonedaEquiv.symm t := by
  obtain ⟨s, hproper, hm⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinear_relative_simplex_lift φ hs hq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryKnownData b) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryKnownData_equation b) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex t)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryKnownData_map_proper φ b t hb)
  have hfaces : ∀ j : Fin (n + 2),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom s.val = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryFaceData b j := by
    intro j
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryKnownData_pullback_face b j]
    funext i
    rcases i with ⟨⟨J, k⟩, hJ, hk⟩
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom s.val).component J k hJ hk =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryKnownData b)).component J k hJ hk
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn]
    exact hproper _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundary_image_ne_univ j J)
  refine ⟨SSet.yonedaEquiv.symm s.toPinched, ?_, ?_⟩
  · apply SSet.boundary.hom_ext
    intro j
    rw [← Category.assoc, SSet.boundary.ι_ι]
    apply SSet.yonedaEquiv.injective
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.apply_symm_apply]
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x y n).injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (s.toPinched.pullback (SimplexCategory.δ j)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_pullback, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched]
    exact Subtype.ext (hfaces j)
  · apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x' y' (n + 1)).injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex φ s.toPinched) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex t
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched, hm]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
