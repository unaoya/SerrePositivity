module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRoofSimplicialReplacement

/-! # 共通宇宙の屋根図式の有限実相対充填

概要：任意の既存屋根を固定する有限相対充填を、AsSmall の共通宇宙の添字へ移す。
方針：元の添字の細分射を反転して持ち上げ、全指定境界と実ホモトピーを保持する。
規約：元の対象・Hom の宇宙は独立。使われ方：simplicial replacement の弱同値比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite DifferentialGraded DGQuotient SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 共通宇宙の指定添字から出る一つの細分で、有限個の正次元の境界を相対充填する。 -/
theorem dgCommonRoofRefinement_relative_fillers (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    {m n : ℕ} (x : D) (y : Fin m → D) (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCommonRoofIndex A D P x)
    (b : ∀ i, (∂Δ[n + 1] : SSet.{max u v}) ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonRoofOriginal A D P x (y i)).obj c)
    (g : ∀ i, ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonRoofConstant A D P x (y i)).obj c) _⦋n + 1⦌)
    (hb : ∀ i, b i ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonRoofComparison A D P x (y i)).app c =
      (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm (g i) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonRoofConstantComparison A D P x (y i)).app c) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCommonRoofIndex A D P x, ∃ r : c ⟶ d,
      ∃ t : ∀ i, ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonRoofOriginal A D P x (y i)).obj d) _⦋n + 1⦌,
        (∀ i, (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm (t i) =
          b i ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonRoofOriginal A D P x (y i)).map r) ∧
        ∀ i, Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofBoundaryFixedHomotopy
          (SSet.yonedaEquiv.symm (g i) ≫
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonRoofConstantComparison A D P x (y i)).app d)
          (SSet.yonedaEquiv.symm (t i) ≫
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonRoofComparison A D P x (y i)).app d)) := by
  cases c with | up c =>
    obtain ⟨s, r, t, ht, hh⟩ :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofRefinement_relative_fillers A D P hP x y c.unop b g hb
    exact ⟨AsSmall.up.obj (op s), AsSmall.up.map r.op, t, ht, hh⟩

/-- 同じ共通宇宙の指定添字から出る一つの細分で、有限個の商頂点を持ち上げる。 -/
theorem dgCommonRoofRefinement_vertex_lifts (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    {m : ℕ} (x : D) (y : Fin m → D) (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCommonRoofIndex A D P x)
    (g : ∀ i, ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonRoofConstant A D P x (y i)).obj c) _⦋0⦌) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCommonRoofIndex A D P x, ∃ _r : c ⟶ d,
      ∃ t : ∀ i, ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonRoofOriginal A D P x (y i)).obj d) _⦋0⦌,
        ∀ i, Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofBoundaryFixedHomotopy
          (SSet.yonedaEquiv.symm (g i) ≫
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonRoofConstantComparison A D P x (y i)).app d)
          (SSet.yonedaEquiv.symm (t i) ≫
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonRoofComparison A D P x (y i)).app d)) := by
  cases c with | up c =>
    obtain ⟨s, r, t, hh⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofRefinement_vertex_lifts A D P hP x y c.unop g
    exact ⟨AsSmall.up.obj (op s), AsSmall.up.map r.op, t, hh⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
