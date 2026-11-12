module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientActualRelativeHomotopies

/-! # 零次元を含む全次数の閉分母後の実係数相対充填

概要：有限な実係数境界と商単体を、一つの追加閉分母後に全境界付きで充填する。
方針：正次数の既存構成に、真部分条件が空となる零次元の構成を接続する。
規約：空の有限族も許す。使われ方：有限相対骨格の全セル次数の充填。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 全次数の実境界・商単体の有限族は、一つの閉分母後に相対充填できる。 -/
theorem dgQuotientFinite_exists_allRelativeHomotopies (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    {m n : ℕ} (x : D) (y : Fin m → D)
    (b : ∀ i, (∂Δ[n] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x (y i))
    (g : ∀ i, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (y i))) _⦋n⦌)
    (hb : ∀ i, b i ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map x (y i)) =
      (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm (g i)) :
    ∃ (q : D) (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x),
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ∧
      ∃ t : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A q (y i) n,
        (∀ i, (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm (t i).toPinched =
          b i ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D s) ∧
        ∀ i, Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedRelativeHomotopy
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap ((inclusion A D P).map q (y i)) (t i))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A (QuotientObject D P)
            (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj q) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
            (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (y i)) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map s))
              (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (g i)))) := by
  cases n with
  | zero =>
    have hfull (J : Finset (Fin 1)) (hJ : J.Nonempty) : J = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro j
      obtain ⟨a, ha⟩ := hJ
      exact (Subsingleton.elim a j) ▸ ha
    obtain ⟨q, s, hs, t, ht, hh⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFinite_exists_pinchedRelativeHomotopies A D P hP
      x y (fun _ => 0) (fun _ J _ hJ _ hne => (hne (hfull J hJ)).elim)
      (fun i => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (g i)) (fun _ J _ hJ _ hne => (hne (hfull J hJ)).elim)
    refine ⟨q, s, hs, t, ?_, hh⟩
    intro i
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨z, hz⟩
    rw [SSet.boundary_zero] at hz
    exact False.elim hz
  | succ n => exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFinite_exists_actualRelativeHomotopies A D P hP x y b g hb

end SerrePositivity.InfinityCategories.Project.DerivedCategories
