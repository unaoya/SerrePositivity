module
public import SerrePositivity.InfinityCategories.Derived.DGSkeletalQuotientExtension

/-! # 有限相対骨格の係数充填の一段更新

概要：共通閉分母、次骨格の元係数、全体商写像と下骨格固定比較を一括して更新する。
方針：有限新セルの同時充填と次骨格の比較の Kan 延長を組み合わせる。
規約：零次元を含み、下骨格の全時刻を固定する。使われ方：一般有限対の帰納。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve SSet MonoidalCategory
open CartesianMonoidalCategory SSet.relativeCellComplexOfMono
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D) {L K : SSet.{max u v}} (i : L ⟶ K) (n : ℕ) (x y : D)
variable (f : (skeletonOfMono i n : SSet) ⟶ DGNerve.pinchedHom A D x y)
variable (g : K ⟶ DGNerve.pinchedHom A (QuotientObject D P)
  ((inclusion A D P).obj x) ((inclusion A D P).obj y))

/-- 相対骨格の一段更新で保持する実データ。 -/
structure DGCoefficientSkeletalStep where
  source : D
  denominator : ForgetEnrichment.of (Complex A) source ⟶ ForgetEnrichment.of (Complex A) x
  denominator_mem : (dgClosedEdge A D denominator).edge ∈ dgVerdierEdges A D P
  sourceMap : (skeletonOfMono i (n + 1) : SSet) ⟶ DGNerve.pinchedHom A D source y
  quotientMap : K ⟶ DGNerve.pinchedHom A (QuotientObject D P)
    ((inclusion A D P).obj source) ((inclusion A D P).obj y)
  previous : r i n ≫ sourceMap = f ≫ pinchedClosedPrecomposition A D denominator
  square : sourceMap ≫ pinchedHomChainMap ((inclusion A D P).map source y) =
    (skeletonOfMono i (n + 1)).ι ≫ quotientMap
  homotopy : SSet.Homotopy
    (g ≫ pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (inclusion A D P).obj source) (x := (inclusion A D P).obj x)
      (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map denominator)) quotientMap
  fixed : ((skeletonOfMono i n).ι ▷ (Δ[1] : SSet.{max u v})) ≫ homotopy.h =
    fst _ _ ≫ (skeletonOfMono i n).ι ≫ g ≫
      pinchedClosedPrecomposition A (QuotientObject D P)
        (q := (inclusion A D P).obj source) (x := (inclusion A D P).obj x)
        (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map denominator)

/-- 各有限骨格段は、一つの追加閉分母後に次の段へ進める。 -/
theorem dgCoefficientSkeletalStep_nonempty [IsDGPretriangulated A D] [K.Finite]
    (hP : localKFlat A D P)
    (hf : f ≫ pinchedHomChainMap ((inclusion A D P).map x y) =
      (skeletonOfMono i n).ι ≫ g) :
    Nonempty (DGCoefficientSkeletalStep A D P i n x y f g) := by
  obtain ⟨C⟩ := dgSkeletalCellRefinement_nonempty A D P i n x y f g hP hf
  obtain ⟨E⟩ := dgSkeletalQuotientExtension_nonempty A D P i n x y f g C hf
  exact ⟨{
    source := C.source
    denominator := C.denominator
    denominator_mem := C.denominator_mem
    sourceMap := C.sourceExtension
    quotientMap := E.map
    previous := DGSkeletalCellRefinement.sourceExtension_previous A D P i n x y f g C
    square := E.square.symm
    homotopy := E.homotopy
    fixed := DGSkeletalQuotientExtension.homotopy_previous A D P i n x y f g E }⟩

end SerrePositivity.InfinityCategories
