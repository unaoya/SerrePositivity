module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGCoefficientSkeletalStage

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet MonoidalCategory
open CartesianMonoidalCategory SSet.relativeCellComplexOfMono
open scoped _root_.Simplicial

/-- 零骨格から指定部分への同型は、全体への包含とも可換する。 -/
lemma skeletonBaseZeroIso_hom_inclusion {L K : SSet.{w}} (i : L ⟶ K) [Mono i] :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBaseZeroIso i).hom ≫ i = (skeletonOfMono i 0).ι := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBaseZeroIso i).inv).1
  rw [Iso.inv_hom_id_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBaseZeroIso_inv]
  rfl

variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable (P : Set D) {L K : SSet.{max u v}} (i : L ⟶ K) [Mono i] (x y : D)
variable (a : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
variable (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P)
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y))

/-- 指定した厳密な係数正方形は、恒等閉分母による零段の状態を持つ。 -/
theorem dgCoefficientSkeletalInitial_nonempty
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map x y) = i ≫ g) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoefficientSkeletalStage A D P i 0 x y a g) := by
  let s := 𝟙 (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
  let p := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D (y := y) s
  let qp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
    (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
    (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map s)
  let f := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBaseZeroIso i).hom ≫ a ≫ p
  let g' := g ≫ qp
  refine ⟨{
    source := x
    denominator := s
    denominator_mem := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominator_id A D P x
    sourceMap := f
    quotientMap := g'
    boundary := ?_
    square := ?_
    homotopy := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl g'
    fixed := ?_ }⟩
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBase i 0 ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBaseZeroIso i).hom ≫ a ≫ p = a ≫ p
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBaseZeroIso_inv, Iso.inv_hom_id_assoc]
  · change ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBaseZeroIso i).hom ≫ a ≫ p) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map x y) = (skeletonOfMono i 0).ι ≫ g ≫ qp
    rw [Category.assoc, Category.assoc]
    dsimp only [p]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition_map_naturality]
    rw [← Category.assoc a, ha]
    simp only [Category.assoc]
    rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBaseZeroIso i).hom, skeletonBaseZeroIso_hom_inclusion]
  · change (i ▷ Δ[1]) ≫ (fst K Δ[1] ≫ g') = fst L Δ[1] ≫ i ≫ g'
    rw [← Category.assoc, whiskerRight_fst, Category.assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
