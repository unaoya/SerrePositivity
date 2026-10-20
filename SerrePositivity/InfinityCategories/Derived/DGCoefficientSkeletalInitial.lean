module
public import SerrePositivity.InfinityCategories.Derived.DGCoefficientSkeletalStage

/-! # 係数骨格の零段の初期状態

概要：相対零骨格と指定部分の同型から、元の境界と商全体を保持する初期状態を作る。
方針：恒等閉分母による前合成を両側で使い、自然性で厳密な正方形を作る。
規約：恒等前合成を簡約せず同じ射のまま保持する。使われ方：有限骨格帰納の開始。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve SSet MonoidalCategory
open CartesianMonoidalCategory SSet.relativeCellComplexOfMono
open scoped Simplicial

/-- 零骨格から指定部分への同型は、全体への包含とも可換する。 -/
lemma skeletonBaseZeroIso_hom_inclusion {L K : SSet.{w}} (i : L ⟶ K) [Mono i] :
    (skeletonBaseZeroIso i).hom ≫ i = (skeletonOfMono i 0).ι := by
  apply (cancel_epi (skeletonBaseZeroIso i).inv).1
  rw [Iso.inv_hom_id_assoc, skeletonBaseZeroIso_inv]
  rfl

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
variable (P : Set D) {L K : SSet.{max u v}} (i : L ⟶ K) [Mono i] (x y : D)
variable (a : L ⟶ DGNerve.pinchedHom A D x y)
variable (g : K ⟶ DGNerve.pinchedHom A (QuotientObject D P)
  ((inclusion A D P).obj x) ((inclusion A D P).obj y))

/-- 指定した厳密な係数正方形は、恒等閉分母による零段の状態を持つ。 -/
theorem dgCoefficientSkeletalInitial_nonempty
    (ha : a ≫ pinchedHomChainMap ((inclusion A D P).map x y) = i ≫ g) :
    Nonempty (DGCoefficientSkeletalStage A D P i 0 x y a g) := by
  let s := 𝟙 (ForgetEnrichment.of (Complex A) x)
  let p := pinchedClosedPrecomposition A D (y := y) s
  let qp := pinchedClosedPrecomposition A (QuotientObject D P)
    (q := (inclusion A D P).obj x) (x := (inclusion A D P).obj x)
    (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map s)
  let f := (skeletonBaseZeroIso i).hom ≫ a ≫ p
  let g' := g ≫ qp
  refine ⟨{
    source := x
    denominator := s
    denominator_mem := dgClosedVerdierDenominator_id A D P x
    sourceMap := f
    quotientMap := g'
    boundary := ?_
    square := ?_
    homotopy := functorHomotopyRefl g'
    fixed := ?_ }⟩
  · change skeletonBase i 0 ≫ (skeletonBaseZeroIso i).hom ≫ a ≫ p = a ≫ p
    rw [← skeletonBaseZeroIso_inv, Iso.inv_hom_id_assoc]
  · change ((skeletonBaseZeroIso i).hom ≫ a ≫ p) ≫
      pinchedHomChainMap ((inclusion A D P).map x y) = (skeletonOfMono i 0).ι ≫ g ≫ qp
    rw [Category.assoc, Category.assoc]
    dsimp only [p]
    rw [pinchedClosedPrecomposition_map_naturality]
    rw [← Category.assoc a, ha]
    simp only [Category.assoc]
    rw [← Category.assoc (skeletonBaseZeroIso i).hom, skeletonBaseZeroIso_hom_inclusion]
  · change (i ▷ Δ[1]) ≫ (fst K Δ[1] ≫ g') = fst L Δ[1] ≫ i ≫ g'
    rw [← Category.assoc, whiskerRight_fst, Category.assoc]

end SerrePositivity.InfinityCategories
