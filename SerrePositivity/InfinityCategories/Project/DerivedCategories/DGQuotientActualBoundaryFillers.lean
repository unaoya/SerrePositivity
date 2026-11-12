module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientPinchedBoundaryFillers
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedBoundaryFromProperComponents

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 全面を保つ実充填と、指定商単体の最上位への比較境界を有限族に同時構成する。 -/
theorem dgQuotientFinite_exists_actualBoundaryFillers (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    {m n : ℕ} (x : D) (y : Fin m → D)
    (b : ∀ i, (∂Δ[n + 1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x (y i))
    (g : ∀ i, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (y i))) _⦋n + 1⦌)
    (hb : ∀ i, b i ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map x (y i)) =
      (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm (g i)) :
    ∃ (q : D) (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x),
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ∧
      ∃ t : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A q (y i) (n + 1),
        (∀ i, (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm (t i).toPinched =
          b i ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D s) ∧
        ∀ i, ∃ e : _root_.SerrePositivity.DifferentialGraded.GradedHom A ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj q) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (y i))
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree (n + 1) - 1),
          (_root_.SerrePositivity.DifferentialGraded.homObject A (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D P) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj q)
            ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (y i))).d
              (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree (n + 1) - 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree (n + 1)) e =
                _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPrimitiveResidual A D (QuotientObject D P) (inclusion A D P)
                  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree (n + 1))
                  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (g i)).val.component Finset.univ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree (n + 1))
                    Finset.univ_nonempty rfl)
                  ((t i).val.component Finset.univ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree (n + 1))
                    Finset.univ_nonempty rfl) s := by
  obtain ⟨q, s, hs, t, ht, he⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFinite_exists_pinchedBoundaryFillers A D P hP
    x y (fun i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryKnownData (b i))
    (fun i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryKnownData_equation (b i)) (fun i => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (g i))
    (fun i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryKnownData_map_proper ((inclusion A D P).map x (y i))
      (b i) (g i) (hb i))
  refine ⟨q, s, hs, t, ?_, he⟩
  intro i
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundary_eq_of_proper_components (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D s) (b i) (t i)
  intro J k hJ hk hne
  exact (ht i J k hJ hk hne).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_f A D s k ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryKnownData (b i)).component J k hJ hk)).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
