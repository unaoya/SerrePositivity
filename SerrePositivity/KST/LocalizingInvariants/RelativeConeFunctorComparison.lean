module

public import SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.VerdierRelativeConeRecovery
public import SerrePositivity.InfinityCategories.F1B.Quasicategory.RelativeComparisonInverse
public import SerrePositivity.InfinityCategories.Core.Quasicategory.RelativeConeProductCurry
public import SerrePositivity.InfinityCategories.Core.SliceConeFamilyEquivalence

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
    (S : SSet.{u}) (hs : HasVerdierRelativeConeRecovery q S)
    (K : SSet.{u}) [K.Finite] (p : K ⟶ (ihom S).obj X)
    (t : JoinCone (p ≫ (ihom S).map q)) :
    ∃ c : JoinCone p, Nonempty (VertexIso (X := sliceOver (p ≫ (ihom S).map q))
      (mapJoinCone ((ihom S).map q) c) t) := by
  let j := joinInr (Δ[0] : SSet.{u}) K
  let P := (β_ K S).hom ≫ uncurry p
  let H := (β_ (join (Δ[0] : SSet.{u}) K) S).hom ≫ uncurry t.val
  have hb : (j ▷ S) ≫ H = P ≫ q := by
    have hn : (j ▷ S) ≫ (β_ (join (Δ[0] : SSet.{u}) K) S).hom =
        (β_ K S).hom ≫ (S ◁ j) := rfl
    change (j ▷ S) ≫ ((β_ _ S).hom ≫ uncurry t.val) = _
    rw [← Category.assoc, hn, Category.assoc, ← uncurry_natural_left, t.property,
      uncurry_natural_right]
    rfl
  obtain ⟨d⟩ := hs K P H hb
  let c : JoinCone p := ⟨curry ((β_ S (join (Δ[0] : SSet.{u}) K)).hom ≫ d.diagram), by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry]
    have hn : (S ◁ j) ≫ (β_ S (join (Δ[0] : SSet.{u}) K)).hom =
        (β_ S K).hom ≫ (j ▷ S) := rfl
    rw [← Category.assoc, hn, Category.assoc, d.boundary]
    change (β_ S K).hom ≫ (β_ K S).hom ≫ uncurry p = uncurry p
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]⟩
  have : Mono (j ▷ S) := (tensorRight S).map_mono j
  have hd : (j ▷ S) ≫ (d.diagram ≫ q) = P ≫ q := by
    rw [← Category.assoc, d.boundary]
  obtain ⟨E⟩ := fixedDiagramVertexIso_of_relativeHomotopy (j ▷ S) (P ≫ q)
    (d.diagram ≫ q) H hd hb d.comparison d.fixed d.invertible
  let r := (pre (j ▷ S)).app Y
  let U := relativeConeProductCurryIso (join (Δ[0] : SSet.{u}) K) S Y
  have hbase : (relativeConeProductCurryIso K S Y).hom.app (Opposite.op ⦋0⦌)
      (functorVertex (P ≫ q)) = functorVertex (p ≫ (ihom S).map q) := by
    rw [_root_.SerrePositivity.InfinityCategories.Core.Quasicategory.relativeConeProductCurryIso_vertex]
    apply congrArg functorVertex
    change curry ((β_ S K).hom ≫ ((β_ K S).hom ≫ uncurry p) ≫ q) = _
    rw [← Category.assoc, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp,
      curry_natural_right, curry_uncurry]
  let m : vertexFiber r (functorVertex (P ≫ q)) ⟶ coneFamily (p ≫ (ihom S).map q) :=
    vertexFiberLift (coneRestriction K ((ihom S).obj Y))
      (functorVertex (p ≫ (ihom S).map q))
      (vertexFiberι r (functorVertex (P ≫ q)) ≫ U.hom) (by
        change vertexFiberι r (functorVertex (P ≫ q)) ≫
          ((relativeConeProductCurryIso (join (Δ[0] : SSet.{u}) K) S Y).hom ≫
            (pre j).app ((ihom S).obj Y)) = _
        rw [← _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.relativeConeProductCurryIso_pre j]
        change vertexFiberι r (functorVertex (P ≫ q)) ≫
          (r ≫ (relativeConeProductCurryIso K S Y).hom) = _
        rw [← Category.assoc, vertexFiberι_comp, SSet.const_comp, hbase])
  have hmc : m.app (Opposite.op ⦋0⦌) (fixedDiagramVertex (j ▷ S) (P ≫ q)
      (d.diagram ≫ q) hd) = (sliceConeFamilyMap (p ≫ (ihom S).map q)).app
        (Opposite.op ⦋0⦌) (mapJoinCone ((ihom S).map q) c) := by
    rw [sliceConeFamilyMap_app_zero]
    apply Subtype.ext
    change U.hom.app (Opposite.op ⦋0⦌) (functorVertex (d.diagram ≫ q)) =
      functorVertex (c.val ≫ (ihom S).map q)
    rw [_root_.SerrePositivity.InfinityCategories.Core.Quasicategory.relativeConeProductCurryIso_vertex]
    apply congrArg functorVertex
    change curry ((β_ S (join (Δ[0] : SSet.{u}) K)).hom ≫ d.diagram ≫ q) =
      curry ((β_ S (join (Δ[0] : SSet.{u}) K)).hom ≫ d.diagram) ≫ (ihom S).map q
    exact curry_natural_right _ _
  have hmt : m.app (Opposite.op ⦋0⦌) (fixedDiagramVertex (j ▷ S) (P ≫ q) H hb) =
      (sliceConeFamilyMap (p ≫ (ihom S).map q)).app (Opposite.op ⦋0⦌) t := by
    rw [sliceConeFamilyMap_app_zero]
    apply Subtype.ext
    change U.hom.app (Opposite.op ⦋0⦌) (functorVertex H) = functorVertex t.val
    rw [_root_.SerrePositivity.InfinityCategories.Core.Quasicategory.relativeConeProductCurryIso_vertex]
    apply congrArg functorVertex
    change curry ((β_ S (join (Δ[0] : SSet.{u}) K)).hom ≫
      (β_ (join (Δ[0] : SSet.{u}) K) S).hom ≫ uncurry t.val) = t.val
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp, curry_uncurry]
  have em := VertexIso.map E m
  change VertexIso (m.app (Opposite.op ⦋0⦌) (fixedDiagramVertex (j ▷ S) (P ≫ q)
    (d.diagram ≫ q) hd)) (m.app (Opposite.op ⦋0⦌)
      (fixedDiagramVertex (j ▷ S) (P ≫ q) H hb)) at em
  rw [hmc, hmt] at em
  exact ⟨c, ⟨((isQCatEquivalence_sliceConeFamilyMap
    (p ≫ (ihom S).map q)).isFullyFaithful).preimageVertexIso em⟩⟩

end SerrePositivity.KST.LocalizingInvariants
