module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientAllRelativeHomotopies
public import SerrePositivity.InfinityCategories.Derived.DGQuotientRoofFiniteFillers

/-! # 全次数の有限係数セル族の実充填と境界固定比較

概要：有限な実係数境界族を、一つの追加閉分母後に同時充填し、商係数と全境界付きで比較する。
方針：全次数の線形相対充填を実 pinched Hom の単体写像へ移す。
規約：零セルと空族を含む。使われ方：一般有限対の相対骨格の一段更新。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve DGNerve.PinchedHom SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 零次元を含む有限セル族は、一つの閉分母後に実充填と境界固定比較を持つ。 -/
theorem dgQuotientFinite_exists_coefficientFillers (P : Set D) (hP : localKFlat A D P)
    {m n : ℕ} (x : D) (y : Fin m → D)
    (b : ∀ i, (∂Δ[n] : SSet.{max u v}) ⟶ DGNerve.pinchedHom A D x (y i))
    (g : ∀ i, (DGNerve.pinchedHom A (QuotientObject D P)
      ((inclusion A D P).obj x) ((inclusion A D P).obj (y i))) _⦋n⦌)
    (hb : ∀ i, b i ≫ pinchedHomChainMap ((inclusion A D P).map x (y i)) =
      (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm (g i)) :
    ∃ (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x),
      (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P ∧
      ∃ t : ∀ i, (DGNerve.pinchedHom A D q (y i)) _⦋n⦌,
        (∀ i, (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm (t i) =
          b i ≫ pinchedClosedPrecomposition A D s) ∧
        ∀ i, Nonempty (RoofBoundaryFixedHomotopy
          (SSet.yonedaEquiv.symm (g i) ≫ pinchedClosedPrecomposition A (QuotientObject D P)
            (y := (inclusion A D P).obj (y i)) ((inclusion A D P).onClosed.map s))
          (SSet.yonedaEquiv.symm (t i) ≫ pinchedHomChainMap ((inclusion A D P).map q (y i)))) := by
  obtain ⟨q, s, hs, t, ht, hh⟩ := dgQuotientFinite_exists_allRelativeHomotopies A D P hP x y b g hb
  refine ⟨q, s, hs, fun i => (t i).toPinched, ht, ?_⟩
  intro i
  let H := Classical.choice (hh i)
  change Nonempty (RoofBoundaryFixedHomotopy
    (SSet.yonedaEquiv.symm (g i) ≫ pinchedHomChainMap _)
    (SSet.yonedaEquiv.symm (t i).toPinched ≫ pinchedHomChainMap _))
  rw [pinchedLinearSimplexMap_yoneda, SSet.yonedaEquiv_symm_comp]
  exact ⟨⟨H.homotopy, H.boundary⟩⟩

end SerrePositivity.InfinityCategories
