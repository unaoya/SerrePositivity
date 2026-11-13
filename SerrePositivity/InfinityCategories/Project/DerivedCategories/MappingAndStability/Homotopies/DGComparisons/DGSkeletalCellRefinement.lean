module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientCoefficientFillers
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.SkeletalCellGluing

/-! # 相対骨格の全新セルの共通閉分母後の係数充填

概要：下骨格の係数写像と全体商写像から、同次数の全新セルを一つの閉分母後に充填する。
方針：有限セル族を Fin に列挙し、全次数の係数充填へ渡す。
規約：零セルと空族も同じ構成に含む。使われ方：一般有限対の係数充填の帰納段階。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet SSet.relativeCellComplexOfMono
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : Set D) {L K : SSet.{max u v}} (i : L ⟶ K) (n : ℕ) (x y : D)
variable (f : (skeletonOfMono i n : SSet) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
variable (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P)
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y))

/-- 全新セルに共通な追加閉分母と、その全実単体・境界固定比較。 -/
structure DGSkeletalCellRefinement where
  source : D
  denominator : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) source ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x
  denominator_mem : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D denominator).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P
  simplex : Cell i n → (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D source y) _⦋n⦌
  boundary (c : Cell i n) : (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm (simplex c) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalCellBoundary i n c ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D denominator
  comparison (c : Cell i n) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofBoundaryFixedHomotopy
    (c.map ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
      (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map denominator))
    (SSet.yonedaEquiv.symm (simplex c) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map source y))

/-- 有限な全新セルに、一つの閉分母後の実係数充填を同時に供給する。 -/
theorem dgSkeletalCellRefinement_nonempty [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] [K.Finite]
    (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (hf : f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map x y) = (skeletonOfMono i n).ι ≫ g) :
    Nonempty (DGSkeletalCellRefinement A D P i n x y f g) := by
  classical
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteSkeletalCells i n
  let := Fintype.ofFinite (Cell i n)
  let e := Fintype.equivFin (Cell i n)
  let bs (j : Fin (Fintype.card (Cell i n))) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalCellBoundary i n (e.symm j) ≫ f
  let gs (j : Fin (Fintype.card (Cell i n))) := SSet.yonedaEquiv ((e.symm j).map ≫ g)
  have hb (j : Fin (Fintype.card (Cell i n))) :
      bs j ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map x y) =
        (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm (gs j) := by
    change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalCellBoundary i n (e.symm j) ≫ f) ≫ _ = _
    rw [Category.assoc, hf, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalCellBoundary_ι, Category.assoc]
    rw [Equiv.symm_apply_apply]
  obtain ⟨q, s, hs, t, ht, hH⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFinite_exists_coefficientFillers A D P hP x
    (fun _ => y) bs gs hb
  refine ⟨{
    source := q
    denominator := s
    denominator_mem := hs
    simplex := fun c => t (e c)
    boundary := ?_
    comparison := ?_ }⟩
  · intro c
    have h := ht (e c)
    simpa only [bs, e.symm_apply_apply, Category.assoc] using h
  · intro c
    have h := Classical.choice (hH (e c))
    simpa only [gs, Equiv.symm_apply_apply, e.symm_apply_apply, Category.assoc] using h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
