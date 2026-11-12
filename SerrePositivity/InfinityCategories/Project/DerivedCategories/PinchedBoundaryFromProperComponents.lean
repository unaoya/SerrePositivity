module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedBoundaryFaceCompatibility

/-! # 全真部分集合の一致から実 pinched 境界の一致へ

概要：鎖写像で写した既知成分を持つ線形単体が、実境界写像を厳密に充填する。
方針：各面の像部分集合は真部分集合なので、成分の一致を面へ引き戻す。
規約：任意の Hom 鎖写像を許す。使われ方：共通実分母による境界充填。
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

/-- 全真部分集合の指定像を保つ線形単体は、実境界の指定像を充填する。 -/
lemma pinchedBoundary_eq_of_proper_components
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject A D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject A E x' y') {n : ℕ}
    (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x' y' (n + 1))
    (hp : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      s.val.component J k hJ hk = φ.f k ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryKnownData b).component J k hJ hk)) :
    (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm s.toPinched = b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap φ := by
  apply SSet.boundary.hom_ext
  intro j
  rw [← Category.assoc, SSet.boundary.ι_ι]
  apply SSet.yonedaEquiv.injective
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.apply_symm_apply,
    ← Category.assoc, SSet.yonedaEquiv_comp]
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x' y' n).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (s.toPinched.pullback (SimplexCategory.δ j)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex φ (SSet.yonedaEquiv (SSet.boundary.ι j ≫ b)))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_pullback, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear]
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom s.val =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryFaceData b j)
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryKnownData_pullback_face, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap_pullback]
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom s.val).component J k hJ hk =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryKnownData b))).component J k hJ hk
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn]
  exact hp _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundary_image_ne_univ j J)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
