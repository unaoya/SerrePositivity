module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedLinearChainMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedProperEquations
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct

/-! # pinched 線形境界と指定された目標成分の同時持ち上げ

概要：全射準同型な Hom 鎖写像に沿って最上位成分を持ち上げる。
方針：削除右辺の閉性と目標単体の方程式を複体の相対原始元持ち上げへ渡す。
規約：真部分集合での一致を仮定する。使われ方：β3 の相対全境界充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
variable [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] {x y : D} {x' y' : E}

/-- 真部分集合を指定通り写す線形データの最上位を指定目標へ持ち上げる。 -/
lemma pinchedLinear_relative_top_lift (φ : _root_.SerrePositivity.DifferentialGraded.homObject A D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject A E x' y')
    (hs : ∀ i : ℤ, Function.Surjective (φ.f i)) (hq : QuasiIso φ)
    {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n)
    (he : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      _root_.SerrePositivity.DifferentialGraded.differential A (f.component J k hJ hk) = f.rhs J k hk)
    (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x' y' n)
    (hm : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      φ.f k (f.component J k hJ hk) = g.val.component J k hJ hk)
    (k : ℤ) (hk : k = 1 - ((Finset.univ : Finset (Fin (n + 1))).card : ℤ)) :
    ∃ q : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y k,
      _root_.SerrePositivity.DifferentialGraded.differential A q = f.rhs Finset.univ k hk ∧
        φ.f k q = g.val.component Finset.univ k (Finset.univ_nonempty) hk := by
  have hr : φ.f (k + 1) (f.rhs Finset.univ k hk) =
      _root_.SerrePositivity.DifferentialGraded.differential A (g.val.component Finset.univ k Finset.univ_nonempty hk) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap_rhs, g.equation]
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinched_rhs_eq_of_proper_components
    exact hm
  let z : _root_.SerrePositivity.DifferentialGraded.complexCycles A (_root_.SerrePositivity.DifferentialGraded.homObject A D x y) (k + 1) :=
    ⟨f.rhs Finset.univ k hk, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinched_rhs_closed_of_proper_equations f he _ _ hk⟩
  exact _root_.SerrePositivity.DifferentialGraded.complex_boundary_lifting_of_surjective_quasiIso A φ hs hq k z _ hr

end SerrePositivity.InfinityCategories.Project.DerivedCategories
