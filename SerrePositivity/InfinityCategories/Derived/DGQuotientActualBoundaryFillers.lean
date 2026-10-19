module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientPinchedBoundaryFillers
public import SerrePositivity.InfinityCategories.Derived.PinchedBoundaryFromProperComponents

/-! # 実 pinched 全境界の有限族の共通 Verdier 分母による充填

概要：商の指定単体を持つ実境界の有限族を、共通の元の実分母の後で充填する。
方針：実境界から全真部分集合を回収し、線形充填の成分の一致を実境界の一致へ戻す。
規約：目標最上位との差の原始元も指定する。使われ方：β3 の相対ホモトピーの構成。
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

/-- 全面を保つ実充填と、指定商単体の最上位への比較境界を有限族に同時構成する。 -/
theorem dgQuotientFinite_exists_actualBoundaryFillers (P : Set D) (hP : localKFlat A D P)
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
        ∀ i, ∃ e : GradedHom A ((inclusion A D P).obj q) ((inclusion A D P).obj (y i))
            (pinchedTopDegree (n + 1) - 1),
          (homObject A (QuotientObject D P) ((inclusion A D P).obj q)
            ((inclusion A D P).obj (y i))).d
              (pinchedTopDegree (n + 1) - 1) (pinchedTopDegree (n + 1)) e =
                dgPrimitiveResidual A D (QuotientObject D P) (inclusion A D P)
                  (pinchedTopDegree (n + 1))
                  ((toLinearSimplex (g i)).val.component Finset.univ (pinchedTopDegree (n + 1))
                    Finset.univ_nonempty rfl)
                  ((t i).val.component Finset.univ (pinchedTopDegree (n + 1))
                    Finset.univ_nonempty rfl) s := by
  obtain ⟨q, s, hs, t, ht, he⟩ := dgQuotientFinite_exists_pinchedBoundaryFillers A D P hP
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
