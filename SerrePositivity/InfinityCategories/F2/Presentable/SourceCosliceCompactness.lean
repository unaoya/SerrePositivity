module

public import SerrePositivity.InfinityCategories.F2.Presentable.SourceDiagonalPullback
public import SerrePositivity.InfinityCategories.F2.Presentable.SourceCosliceFilteredColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.NativeBaseChangePreservation
public import SerrePositivity.InfinityCategories.F2.Presentable.IdentityClassificationPreservation
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.EdgeCosliceMappingFiber
public import SerrePositivity.InfinityCategories.F2.Presentable.Aleph0CardinalChangeBound
public import SerrePositivity.InfinityCategories.F1.Compact.RepresentableCoslice
public import SerrePositivity.InfinityCategories.HomotopyLimits.SimplexTerminalCosliceFiber

/-!
概要：compact な両端を持つ元の射は、固定始域 coslice 内でも compact となる。
方針：辺全体の coslice の分類を終点の Hom に比較し、始点の Hom との対角引き戻しを使う。
規約：元の辺と coslice を保持し、fiber の accessibility を入力にしない。
使われ方：指定した表示段からの境界を保つ compact 因子化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：compact 対象からの元の coslice 射影の全分類は filtered 余極限を保存する。
方針：全共変 Hom との元の分類比較を使う。
規約：同じ濃度・同じ小さい試験添字。
使われ方：対角引き戻しの始点側の分類。 -/
lemma compactSourceClassification_preservesKappaFilteredColimits
    {μ : Cardinal.{u}} {C : SSet.{u + 1}} [Quasicategory C] {x : C _⦋0⦌}
    (hx : Compact.IsKappaCompact.{u, u + 1} μ x) :
    Compact.PreservesKappaFilteredColimits.{u, u + 1} μ
      (leftStraighteningInfinityDiagram (sliceUnderProjection (SSet.yonedaEquiv.symm x))) :=
  hx.of_functorIso (Compact.covariantRepresentableInfinity_cosliceIso x)

/-- 概要：終点が compact な元の辺全体の coslice の分類は filtered 余極限を保存する。
方針：最後の頂点への right anodyne 制限を底上の分類同型に移す。
規約：元の辺全体の全空間を保つ。
使われ方：対角引き戻しの終点側の分類。 -/
lemma edgeTargetClassification_preservesKappaFilteredColimits
    {μ : Cardinal.{u}} {C : SSet.{u + 1}} [Quasicategory C]
    {x y : C _⦋0⦌} (f : C.Edge x y) (hy : Compact.IsKappaCompact.{u, u + 1} μ y) :
    Compact.PreservesKappaFilteredColimits.{u, u + 1} μ
      (leftStraighteningInfinityDiagram (sliceUnderProjection (SSet.yonedaEquiv.symm f.edge))) := by
  let a := SSet.yonedaEquiv.symm f.edge
  let i : (Δ[0] : SSet.{u + 1}) ⟶ Δ[1] := SSet.stdSimplex.δ 0
  have hi : i ≫ a = SSet.yonedaEquiv.symm y := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact f.tgt_eq
  have htf : TrivialKanFibration (sliceUnderRestrict a i) :=
    sliceUnderRestrict_trivialKanFibration a i endpointInclusion_rightAnodyne
  have := htf
  let r := sliceUnderRestrict a i ≫ eqToHom (congrArg sliceUnder hi)
  have hrq := (qCatEquivalenceOfTrivialKanFibration
    (sliceUnderRestrict a i)).isQCatEquivalence.comp
      (qCatEquivalenceOfIso (eqToIso (congrArg sliceUnder hi))).isQCatEquivalence
  have hr : IsPrecompositionEquivalence r := hrq.isPrecompositionEquivalence
  have hp : r ≫ sliceUnderProjection (SSet.yonedaEquiv.symm y) = sliceUnderProjection a :=
    normalizedCoconeRestriction_projection a i hi
  exact (compactSourceClassification_preservesKappaFilteredColimits hy).of_functorIso
    (Compact.leftClassification_of_precompositionEquivalence (sliceUnderProjection a)
      (sliceUnderProjection (SSet.yonedaEquiv.symm y)) r hp hr).symm

/-- 概要：compact な両端を持つ射は、始点の下の元の coslice 内で compact。
方針：全 Hom の分類を、両端の Hom と一点分類の対角引き戻しで保存と判定する。
規約：coslice の accessibility と一般の引き戻し accessibility は使わない。
使われ方：元の表示段を保った交互構成の相対因子化。 -/
lemma isKappaCompact_edgeCosliceVertex
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {C : SSet.{u + 1}} [Quasicategory C] {x y : C _⦋0⦌} (f : C.Edge x y)
    (hx : Compact.IsKappaCompact.{u, u + 1} μ x)
    (hy : Compact.IsKappaCompact.{u, u + 1} μ y) :
    Compact.IsKappaCompact.{u, u + 1} μ (edgeCosliceVertex f.toTruncated) := by
  let q := Localization.edgeCosliceSourceRestriction f
  let d := sliceUnderProjection (SSet.yonedaEquiv.symm x)
  have hq : q = (Localization.edgeCosliceUnderIso f).hom ≫
      sliceUnderProjection (SSet.yonedaEquiv.symm (edgeCosliceVertex f.toTruncated)) :=
    (Localization.edgeCosliceUnderIso_projection f).symm
  have : LeftFibration q := by
    rw [hq]
    exact ⟨leftFibrations.comp_mem _ _ (MorphismProperty.of_isIso leftFibrations _)
      (LeftFibration.mem (p := sliceUnderProjection
        (SSet.yonedaEquiv.symm (edgeCosliceVertex f.toTruncated))))⟩
  have hqd : q ≫ d = sliceUnderProjection (SSet.yonedaEquiv.symm f.edge) :=
    Localization.edgeCosliceSourceRestriction_projection f
  have : LeftFibration (q ≫ d) := by rw [hqd]; infer_instance
  have ht : Compact.PreservesKappaFilteredColimits.{u, u + 1} μ
      (leftStraighteningInfinityDiagram (q ≫ d)) := by
    simpa only [hqd] using edgeTargetClassification_preservesKappaFilteredColimits f hy
  have hd := sourceCosliceProjection_isKappaAccessibleFunctor (Fact.out : μ.IsRegular) x
  have he := leftClassification_baseChange_fst_preservesKappaFilteredColimits (q ≫ d) d hd ht
  have hb := leftClassification_baseChange_fst_preservesKappaFilteredColimits d d hd
    (compactSourceClassification_preservesKappaFilteredColimits hx)
  have : Fact Cardinal.aleph0.{u}.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  have hc := sourceDiagonalClassification_preservesKappaFilteredColimits
    (cardinalChangeBound_aleph0 hμ) q d he
    (identityClassification_preservesKappaFilteredColimits hμ.le _) hb
  have hc' := hc.of_functorIso (Compact.leftClassification_overIso q
    (sliceUnderProjection (SSet.yonedaEquiv.symm (edgeCosliceVertex f.toTruncated)))
    (Localization.edgeCosliceUnderIso f) hq.symm)
  exact hc'.of_functorIso
    (Compact.covariantRepresentableInfinity_cosliceIso (edgeCosliceVertex f.toTruncated)).symm

end SerrePositivity.InfinityCategories.F2.Presentable
