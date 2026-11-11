module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalQuotientExtension

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet MonoidalCategory
open CartesianMonoidalCategory SSet.relativeCellComplexOfMono
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : Set D) {L K : SSet.{max u v}} (i : L ⟶ K) (n : ℕ) (x y : D)
variable (f : (skeletonOfMono i n : SSet) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
variable (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P)
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y))

/-- 相対骨格の一段更新で保持する実データ。 -/
structure DGCoefficientSkeletalStep where
  source : D
  denominator : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) source ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x
  denominator_mem : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D denominator).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P
  sourceMap : (skeletonOfMono i (n + 1) : SSet) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D source y
  quotientMap : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P)
    ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj source) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)
  previous : r i n ≫ sourceMap = f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D denominator
  square : sourceMap ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map source y) =
    (skeletonOfMono i (n + 1)).ι ≫ quotientMap
  homotopy : SSet.Homotopy
    (g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
      (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map denominator)) quotientMap
  fixed : ((skeletonOfMono i n).ι ▷ (Δ[1] : SSet.{max u v})) ≫ homotopy.h =
    fst _ _ ≫ (skeletonOfMono i n).ι ≫ g ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
        (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
        (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map denominator)

/-- 各有限骨格段は、一つの追加閉分母後に次の段へ進める。 -/
theorem dgCoefficientSkeletalStep_nonempty [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] [K.Finite]
    (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (hf : f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map x y) =
      (skeletonOfMono i n).ι ≫ g) :
    Nonempty (DGCoefficientSkeletalStep A D P i n x y f g) := by
  obtain ⟨C⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSkeletalCellRefinement_nonempty A D P i n x y f g hP hf
  obtain ⟨E⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSkeletalQuotientExtension_nonempty A D P i n x y f g C hf
  exact ⟨{
    source := C.source
    denominator := C.denominator
    denominator_mem := C.denominator_mem
    sourceMap := C.sourceExtension
    quotientMap := E.map
    previous := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalCellRefinement.sourceExtension_previous A D P i n x y f g C
    square := E.square.symm
    homotopy := E.homotopy
    fixed := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalQuotientExtension.homotopy_previous A D P i n x y f g E }⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
