module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientFiniteRelativePrimitives
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedClosedPrecomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedCompleteTop

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 全指定境界を共通実分母で前合成して充填し、商の最上位との比較境界も得る。 -/
theorem dgQuotientFinite_exists_pinchedBoundaryFillers (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    {m n : ℕ} (x : D) (y : Fin m → D) (f : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x (y i) n)
    (he : ∀ i J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      _root_.SerrePositivity.DifferentialGraded.differential A ((f i).component J k hJ hk) = (f i).rhs J k hk)
    (g : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A ((inclusion A D P).obj x) ((inclusion A D P).obj (y i)) n)
    (hm : ∀ i J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).map x (y i)).f k ((f i).component J k hJ hk) =
        (g i).val.component J k hJ hk) :
    ∃ (q : D) (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x),
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ∧
      ∃ t : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A q (y i) n,
        (∀ i J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
          (t i).val.component J k hJ hk =
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k ((f i).component J k hJ hk) s) ∧
        ∀ i, ∃ b : _root_.SerrePositivity.DifferentialGraded.GradedHom A ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj q) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (y i))
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree n - 1),
          (_root_.SerrePositivity.DifferentialGraded.homObject A (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D P) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj q)
            ((inclusion A D P).obj (y i))).d (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree n - 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree n) b =
              _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPrimitiveResidual A D (QuotientObject D P) (inclusion A D P)
                (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree n)
                ((g i).val.component Finset.univ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree n) Finset.univ_nonempty rfl)
                ((t i).val.component Finset.univ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree n) Finset.univ_nonempty rfl)
                s := by
  let F := _root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P
  let k := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree n
  let a := fun i => (f i).rhs Finset.univ k rfl
  let c := fun i => (g i).val.component Finset.univ k Finset.univ_nonempty rfl
  have ha : ∀ i, _root_.SerrePositivity.DifferentialGraded.differential A (a i) = 0 := fun i =>
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinched_rhs_closed_of_proper_equations (f i) (he i) Finset.univ k rfl
  have hc : ∀ i, _root_.SerrePositivity.DifferentialGraded.differential A (c i) = (F.map x (y i)).f (k + 1) (a i) := by
    intro i
    symm
    change (F.map x (y i)).f (k + 1) ((f i).rhs Finset.univ k rfl) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap_rhs, (g i).equation]
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinched_rhs_eq_of_proper_components
    exact hm i
  obtain ⟨q, s, hs, hw⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFinite_exists_relativePrimitives A D P hP x y
    (fun _ => k) a ha c hc
  choose h hh b hb using hw
  let t := fun i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedCompleteTop (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposeData A D s (f i))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposeData_proper_equations A D s (f i) (he i)) (h i)
    ((hh i).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposeData_rhs A D s (f i) Finset.univ k rfl).symm)
  refine ⟨q, s, hs, t, ?_, ?_⟩
  · intro i J l hJ hl hne
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedCompleteTopData_proper _ (h i) J l hJ hl hne).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposeData_component A D s (f i) J l hJ hl)
  · intro i
    refine ⟨b i, ?_⟩
    change _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPrimitiveResidual A D (QuotientObject D P) F k (c i)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedCompleteTopData _ (h i)).component Finset.univ k Finset.univ_nonempty rfl) s
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedCompleteTopData_full]
    exact hb i

end SerrePositivity.InfinityCategories.Project.DerivedCategories
