module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.VerdierRelativeConeRecovery
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.RelativeComparisonInverse
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.RelativeConeProductCurry
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SliceConeFamilyEquivalence

/-!
概要：積上の境界付き商錐回収を、関手圏の元の slice 内の全錐比較へ移す。
方針：境界固定の円柱を fixed-diagram fiber に入れ、currying で写し slice へ反映する。
規約：同じ実錐と元の全商錐を比較し、境界を忘れた全関手同型で代用しない。
使われ方：c5 の元の core 逆像射影に Quillen A を適用するための有限商錐回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 元の積上の相対回収は、同じ関手図式の slice 内の全錐同型付き回収を与える。 -/
lemma quotientFunctorConeIsoRecovery_of_relativeConeRecovery
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (q : X ⟶ Y)
    (S : SSet.{u}) (hs : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.HasVerdierRelativeConeRecovery q S)
    (K : SSet.{u}) [K.Finite] (p : K ⟶ (ihom S).obj X)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (p ≫ (ihom S).map q)) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (p ≫ (ihom S).map q))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone ((ihom S).map q) c) t) := by
  let j := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K
  let P := (β_ K S).hom ≫ uncurry p
  let H := (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K) S).hom ≫ uncurry t.val
  have hb : (j ▷ S) ≫ H = P ≫ q := by
    have hn : (j ▷ S) ≫ (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K) S).hom =
        (β_ K S).hom ≫ (S ◁ j) := rfl
    change (j ▷ S) ≫ ((β_ _ S).hom ≫ uncurry t.val) = _
    rw [← Category.assoc, hn, Category.assoc, ← uncurry_natural_left, t.property,
      uncurry_natural_right]
    rfl
  obtain ⟨d⟩ := hs K P H hb
  let c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p := ⟨curry ((β_ S (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K)).hom ≫ d.diagram), by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry]
    have hn : (S ◁ j) ≫ (β_ S (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K)).hom =
        (β_ S K).hom ≫ (j ▷ S) := rfl
    rw [← Category.assoc, hn, Category.assoc, d.boundary]
    change (β_ S K).hom ≫ (β_ K S).hom ≫ uncurry p = uncurry p
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]⟩
  have : Mono (j ▷ S) := (tensorRight S).map_mono j
  have hd : (j ▷ S) ≫ (d.diagram ≫ q) = P ≫ q := by
    rw [← Category.assoc, d.boundary]
  obtain ⟨E⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.fixedDiagramVertexIso_of_relativeHomotopy (j ▷ S) (P ≫ q)
    (d.diagram ≫ q) H hd hb d.comparison d.fixed d.invertible
  let r := (pre (j ▷ S)).app Y
  let U := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.relativeConeProductCurryIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K) S Y
  have hbase : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.relativeConeProductCurryIso K S Y).hom.app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (P ≫ q)) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (p ≫ (ihom S).map q) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.relativeConeProductCurryIso_vertex]
    apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
    change curry ((β_ S K).hom ≫ ((β_ K S).hom ≫ uncurry p) ≫ q) = _
    rw [← Category.assoc, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp,
      curry_natural_right, curry_uncurry]
  let m : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber r (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (P ≫ q)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamily (p ≫ (ihom S).map q) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K ((ihom S).obj Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (p ≫ (ihom S).map q))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι r (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (P ≫ q)) ≫ U.hom) (by
        change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι r (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (P ≫ q)) ≫
          ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.relativeConeProductCurryIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K) S Y).hom ≫
            (pre j).app ((ihom S).obj Y)) = _
        rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.relativeConeProductCurryIso_pre j]
        change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι r (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (P ≫ q)) ≫
          (r ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.relativeConeProductCurryIso K S Y).hom) = _
        rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp, hbase])
  have hmc : m.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedDiagramVertex (j ▷ S) (P ≫ q)
      (d.diagram ≫ q) hd) = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap (p ≫ (ihom S).map q)).app
        (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone ((ihom S).map q) c) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap_app_zero]
    apply Subtype.ext
    change U.hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (d.diagram ≫ q)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (c.val ≫ (ihom S).map q)
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.relativeConeProductCurryIso_vertex]
    apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
    change curry ((β_ S (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K)).hom ≫ d.diagram ≫ q) =
      curry ((β_ S (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K)).hom ≫ d.diagram) ≫ (ihom S).map q
    exact curry_natural_right _ _
  have hmt : m.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedDiagramVertex (j ▷ S) (P ≫ q) H hb) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap (p ≫ (ihom S).map q)).app (Opposite.op ⦋0⦌) t := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap_app_zero]
    apply Subtype.ext
    change U.hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.val
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.relativeConeProductCurryIso_vertex]
    apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
    change curry ((β_ S (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K)).hom ≫
      (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K) S).hom ≫ uncurry t.val) = t.val
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp, curry_uncurry]
  have em := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map E m
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (m.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedDiagramVertex (j ▷ S) (P ≫ q)
    (d.diagram ≫ q) hd)) (m.app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedDiagramVertex (j ▷ S) (P ≫ q) H hb)) at em
  rw [hmc, hmt] at em
  exact ⟨c, ⟨((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_sliceConeFamilyMap
    (p ≫ (ihom S).map q)).isFullyFaithful).preimageVertexIso em⟩⟩

end SerrePositivity.KST.LocalizingInvariants
