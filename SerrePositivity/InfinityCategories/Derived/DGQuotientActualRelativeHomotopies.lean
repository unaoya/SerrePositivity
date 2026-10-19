module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientPinchedRelativeHomotopies
public import SerrePositivity.InfinityCategories.Derived.PinchedBoundaryFromProperComponents

/-! # 実 pinched 境界の有限族の指定商単体への相対ホモトピー充填

概要：共通実分母後で全実境界を充填し、商像を指定目標と全境界上定値の実ホモトピーで比較。
方針：回収した線形境界へ有限相対充填を適用し、既知成分の一致を実境界へ戻す。
規約：全指定面を厳密に保つ。使われ方：β3 の実写像空間の局所化普遍性への入力。
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

/-- 全面を保つ実充填と、指定商単体への全境界上定値の実ホモトピーを同時に得る。 -/
theorem dgQuotientFinite_exists_actualRelativeHomotopies (P : Set D) (hP : localKFlat A D P)
    {m n : ℕ} (x : D) (y : Fin m → D)
    (b : ∀ i, (∂Δ[n + 1] : SSet.{max u v}) ⟶ DGNerve.pinchedHom A D x (y i))
    (g : ∀ i, (DGNerve.pinchedHom A (QuotientObject D P)
      ((inclusion A D P).obj x) ((inclusion A D P).obj (y i))) _⦋n + 1⦌)
    (hb : ∀ i, b i ≫ pinchedHomChainMap ((inclusion A D P).map x (y i)) =
      (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm (g i)) :
    ∃ (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x),
      (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P ∧
      ∃ t : ∀ i, LinearSimplex A q (y i) (n + 1),
        (∀ i, (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm (t i).toPinched =
          b i ≫ pinchedClosedPrecomposition A D s) ∧
        ∀ i, Nonempty (PinchedRelativeHomotopy
          (pinchedLinearSimplexMap ((inclusion A D P).map q (y i)) (t i))
          (pinchedLinearSimplexMap (dgClosedPrecomposition A (QuotientObject D P)
            (q := (inclusion A D P).obj q) (x := (inclusion A D P).obj x)
            (y := (inclusion A D P).obj (y i)) ((inclusion A D P).onClosed.map s))
              (toLinearSimplex (g i)))) := by
  obtain ⟨q, s, hs, t, ht, he⟩ := dgQuotientFinite_exists_pinchedRelativeHomotopies A D P hP
    x y (fun i => pinchedBoundaryKnownData (b i))
    (fun i => pinchedBoundaryKnownData_equation (b i)) (fun i => toLinearSimplex (g i))
    (fun i => pinchedBoundaryKnownData_map_proper ((inclusion A D P).map x (y i))
      (b i) (g i) (hb i))
  refine ⟨q, s, hs, t, ?_, he⟩
  intro i
  apply pinchedBoundary_eq_of_proper_components (dgClosedPrecomposition A D s) (b i) (t i)
  intro J k hJ hk hne
  exact (ht i J k hJ hk hne).trans
    (dgClosedPrecomposition_f A D s k ((pinchedBoundaryKnownData (b i)).component J k hJ hk)).symm

end SerrePositivity.InfinityCategories
