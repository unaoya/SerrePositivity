module
public import SerrePositivity.InfinityCategories.Derived.PinchedLinearChainMap
public import SerrePositivity.InfinityCategories.Derived.PinchedProperEquations
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
variable [DGCategory A D] [DGCategory A E] {x y : D} {x' y' : E}

/-- 真部分集合を指定通り写す線形データの最上位を指定目標へ持ち上げる。 -/
lemma pinchedLinear_relative_top_lift (φ : homObject A D x y ⟶ homObject A E x' y')
    (hs : ∀ i : ℤ, Function.Surjective (φ.f i)) (hq : QuasiIso φ)
    {n : ℕ} (f : LinearData A x y n)
    (he : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      differential A (f.component J k hJ hk) = f.rhs J k hk)
    (g : LinearSimplex A x' y' n)
    (hm : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      φ.f k (f.component J k hJ hk) = g.val.component J k hJ hk)
    (k : ℤ) (hk : k = 1 - ((Finset.univ : Finset (Fin (n + 1))).card : ℤ)) :
    ∃ q : GradedHom A x y k,
      differential A q = f.rhs Finset.univ k hk ∧
        φ.f k q = g.val.component Finset.univ k (Finset.univ_nonempty) hk := by
  have hr : φ.f (k + 1) (f.rhs Finset.univ k hk) =
      differential A (g.val.component Finset.univ k Finset.univ_nonempty hk) := by
    rw [pinchedLinearDataMap_rhs, g.equation]
    apply pinched_rhs_eq_of_proper_components
    exact hm
  let z : complexCycles A (homObject A D x y) (k + 1) :=
    ⟨f.rhs Finset.univ k hk, pinched_rhs_closed_of_proper_equations f he _ _ hk⟩
  exact complex_boundary_lifting_of_surjective_quasiIso A φ hs hq k z _ hr

end SerrePositivity.InfinityCategories
