module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientCoefficientFillers
public import SerrePositivity.InfinityCategories.Derived.SkeletalCellGluing

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve SSet SSet.relativeCellComplexOfMono
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D) {L K : SSet.{max u v}} (i : L ⟶ K) (n : ℕ) (x y : D)
variable (f : (skeletonOfMono i n : SSet) ⟶ DGNerve.pinchedHom A D x y)
variable (g : K ⟶ DGNerve.pinchedHom A (QuotientObject D P)
  ((inclusion A D P).obj x) ((inclusion A D P).obj y))

/-- 全新セルに共通な追加閉分母と、その全実単体・境界固定比較。 -/
structure DGSkeletalCellRefinement where
  source : D
  denominator : ForgetEnrichment.of (Complex A) source ⟶ ForgetEnrichment.of (Complex A) x
  denominator_mem : (dgClosedEdge A D denominator).edge ∈ dgVerdierEdges A D P
  simplex : Cell i n → (DGNerve.pinchedHom A D source y) _⦋n⦌
  boundary (c : Cell i n) : (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm (simplex c) =
    skeletalCellBoundary i n c ≫ f ≫ pinchedClosedPrecomposition A D denominator
  comparison (c : Cell i n) : RoofBoundaryFixedHomotopy
    (c.map ≫ g ≫ pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (inclusion A D P).obj source) (x := (inclusion A D P).obj x)
      (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map denominator))
    (SSet.yonedaEquiv.symm (simplex c) ≫ pinchedHomChainMap ((inclusion A D P).map source y))

/-- 有限な全新セルに、一つの閉分母後の実係数充填を同時に供給する。 -/
theorem dgSkeletalCellRefinement_nonempty [IsDGPretriangulated A D] [K.Finite]
    (hP : localKFlat A D P)
    (hf : f ≫ pinchedHomChainMap ((inclusion A D P).map x y) = (skeletonOfMono i n).ι ≫ g) :
    Nonempty (DGSkeletalCellRefinement A D P i n x y f g) := by
  classical
  let := finiteSkeletalCells i n
  let := Fintype.ofFinite (Cell i n)
  let e := Fintype.equivFin (Cell i n)
  let bs (j : Fin (Fintype.card (Cell i n))) := skeletalCellBoundary i n (e.symm j) ≫ f
  let gs (j : Fin (Fintype.card (Cell i n))) := SSet.yonedaEquiv ((e.symm j).map ≫ g)
  have hb (j : Fin (Fintype.card (Cell i n))) :
      bs j ≫ pinchedHomChainMap ((inclusion A D P).map x y) =
        (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm (gs j) := by
    change (skeletalCellBoundary i n (e.symm j) ≫ f) ≫ _ = _
    rw [Category.assoc, hf, ← Category.assoc, skeletalCellBoundary_ι, Category.assoc]
    rw [Equiv.symm_apply_apply]
  obtain ⟨q, s, hs, t, ht, hH⟩ := dgQuotientFinite_exists_coefficientFillers A D P hP x
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

end SerrePositivity.InfinityCategories
