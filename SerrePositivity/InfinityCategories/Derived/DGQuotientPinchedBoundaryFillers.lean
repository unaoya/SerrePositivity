module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientFiniteRelativePrimitives
public import SerrePositivity.InfinityCategories.Derived.PinchedClosedPrecomposition
public import SerrePositivity.InfinityCategories.Derived.PinchedCompleteTop

/-! # 有限個の指定 pinched 線形境界の共通分母による充填

概要：商で指定された単体の有限族に、全真部分集合を保つ元の線形単体を構成する。
方針：閉じた削除右辺と指定最上位成分を相対原始元へ渡し、最上位だけを補う。
規約：商の最上位との比較は指定された境界を伴う。使われ方：β3 の実相対比較への入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve DGNerve.PinchedHom
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 全指定境界を共通実分母で前合成して充填し、商の最上位との比較境界も得る。 -/
theorem dgQuotientFinite_exists_pinchedBoundaryFillers (P : Set D) (hP : localKFlat A D P)
    {m n : ℕ} (x : D) (y : Fin m → D) (f : ∀ i, LinearData A x (y i) n)
    (he : ∀ i J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      differential A ((f i).component J k hJ hk) = (f i).rhs J k hk)
    (g : ∀ i, LinearSimplex A ((inclusion A D P).obj x) ((inclusion A D P).obj (y i)) n)
    (hm : ∀ i J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      ((inclusion A D P).map x (y i)).f k ((f i).component J k hJ hk) =
        (g i).val.component J k hJ hk) :
    ∃ (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x),
      (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P ∧
      ∃ t : ∀ i, LinearSimplex A q (y i) n,
        (∀ i J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
          (t i).val.component J k hJ hk =
            dgGradedPrecompose A D k ((f i).component J k hJ hk) s) ∧
        ∀ i, ∃ b : GradedHom A ((inclusion A D P).obj q) ((inclusion A D P).obj (y i))
            (pinchedTopDegree n - 1),
          (homObject A (QuotientObject D P) ((inclusion A D P).obj q)
            ((inclusion A D P).obj (y i))).d (pinchedTopDegree n - 1) (pinchedTopDegree n) b =
              dgPrimitiveResidual A D (QuotientObject D P) (inclusion A D P)
                (pinchedTopDegree n)
                ((g i).val.component Finset.univ (pinchedTopDegree n) Finset.univ_nonempty rfl)
                ((t i).val.component Finset.univ (pinchedTopDegree n) Finset.univ_nonempty rfl)
                s := by
  let F := inclusion A D P
  let k := pinchedTopDegree n
  let a := fun i => (f i).rhs Finset.univ k rfl
  let c := fun i => (g i).val.component Finset.univ k Finset.univ_nonempty rfl
  have ha : ∀ i, differential A (a i) = 0 := fun i =>
    pinched_rhs_closed_of_proper_equations (f i) (he i) Finset.univ k rfl
  have hc : ∀ i, differential A (c i) = (F.map x (y i)).f (k + 1) (a i) := by
    intro i
    symm
    change (F.map x (y i)).f (k + 1) ((f i).rhs Finset.univ k rfl) = _
    rw [pinchedLinearDataMap_rhs, (g i).equation]
    apply pinched_rhs_eq_of_proper_components
    exact hm i
  obtain ⟨q, s, hs, hw⟩ := dgQuotientFinite_exists_relativePrimitives A D P hP x y
    (fun _ => k) a ha c hc
  choose h hh b hb using hw
  let t := fun i => pinchedCompleteTop (pinchedClosedPrecomposeData A D s (f i))
    (pinchedClosedPrecomposeData_proper_equations A D s (f i) (he i)) (h i)
    ((hh i).trans (pinchedClosedPrecomposeData_rhs A D s (f i) Finset.univ k rfl).symm)
  refine ⟨q, s, hs, t, ?_, ?_⟩
  · intro i J l hJ hl hne
    exact (pinchedCompleteTopData_proper _ (h i) J l hJ hl hne).trans
      (pinchedClosedPrecomposeData_component A D s (f i) J l hJ hl)
  · intro i
    refine ⟨b i, ?_⟩
    change _ = dgPrimitiveResidual A D (QuotientObject D P) F k (c i)
      ((pinchedCompleteTopData _ (h i)).component Finset.univ k Finset.univ_nonempty rfl) s
    rw [pinchedCompleteTopData_full]
    exact hb i

end SerrePositivity.InfinityCategories
