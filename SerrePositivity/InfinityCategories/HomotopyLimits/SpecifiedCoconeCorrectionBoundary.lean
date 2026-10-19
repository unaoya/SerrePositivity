module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightHomTriangle

/-!
概要：指定右修正辺上の全 Hom の族を、元の span が指定した共通部分の境界経路上へ移す。
方針：修正辺の fiber 内の厳密な像を coslice の射へ移し、三角形の族をそのまま後合成する。
規約：境界で別の経路を選ばず、全 Hom の族と元の余錐族への終点評価を保持する。
使われ方：共通 path end における右枝と指定境界経路の全パラメータでの照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p))

/-- 指定右修正辺の共通部分への像は、元の指定境界経路の辺そのもの。 -/
lemma specifiedCoconeCorrectionCoslice_boundary :
    SSet.yonedaEquiv.symm (partialColimitSpecifiedCorrectionCosliceEdge hp p c hc dB dC).edge ≫
        normalizedCoconeRestriction (j ≫ p) g (coconePushoutBoundary_eq hp p) =
      SSet.yonedaEquiv.symm (intervalFunctorVertexEdge (SSet.yonedaEquiv
        (partialColimitSpanBoundaryPath c hc f (i ≫ p) rfl dB
          g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)).val).val := by
  rw [SSet.yonedaEquiv_symm_comp]
  apply congrArg SSet.yonedaEquiv.symm
  let z := (partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).vertex
  let r := normalizedCoconeRestriction (j ≫ p) g (coconePushoutBoundary_eq hp p)
  have hι := vertexFiberMap_ι (sliceUnderProjection (j ≫ p))
    (sliceUnderProjection (f ≫ (i ≫ p))) r
    (normalizedCoconeRestriction_projection (j ≫ p) g (coconePushoutBoundary_eq hp p)) z
  have h := congrArg (fun a : coconeMappingSpace (j ≫ p) z ⟶ sliceUnder (f ≫ (i ≫ p)) ↦
    a.app (Opposite.op ⦋1⦌) (partialColimitSpecifiedCorrectionEdge hp p c hc dB dC).edge) hι
  have h' := congrArg Subtype.val
    (partialColimitSpecifiedCorrectionEdge_projection hp p c hc dB dC)
  have hh := h.symm.trans h'
  dsimp only [r, NatTrans.comp_app, vertexFiberι] at hh
  simp only [types_comp_apply, TypeCat.ofHom_apply] at hh
  simpa only [partialColimitSpecifiedCorrectionCosliceEdge, SSet.Edge.edge,
    SSet.Edge.toTruncated] using hh

/-- 三角形から得た全 Hom の修正族を、元の指定境界経路自身の辺上へ送った族。 -/
def specifiedCoconeBoundaryCorrectionFullHomFamily (y : SpaceInfinity.{u} _⦋0⦌) :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      sliceUnder (SSet.yonedaEquiv.symm (intervalFunctorVertexEdge (SSet.yonedaEquiv
        (partialColimitSpanBoundaryPath c hc f (i ≫ p) rfl dB
          g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)).val).val) :=
  (specifiedCoconeCorrectionFullHomFamily hp p c hc dB dC y ≫
    sliceUnderPostcomp
      (SSet.yonedaEquiv.symm (partialColimitSpecifiedCorrectionCosliceEdge hp p c hc dB dC).edge)
      (normalizedCoconeRestriction (j ≫ p) g (coconePushoutBoundary_eq hp p))) ≫
    eqToHom (congrArg sliceUnder (specifiedCoconeCorrectionCoslice_boundary hp p c hc dB dC))

/-- 共通部分の指定境界辺上の族は、終点で元の全 Hom の余錐族の共通部分への制限を回収する。 -/
lemma specifiedCoconeBoundaryCorrectionFullHomFamily_endpoint (y : SpaceInfinity.{u} _⦋0⦌) :
    specifiedCoconeBoundaryCorrectionFullHomFamily hp p c hc dB dC y ≫
        sliceUnderProjection (SSet.yonedaEquiv.symm (intervalFunctorVertexEdge (SSet.yonedaEquiv
          (partialColimitSpanBoundaryPath c hc f (i ≫ p) rfl dB
            g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)).val).val) =
      coconePointHomFamily (partialColimitSpecifiedPathCocone hp p c hc dB dC) y ≫
        cosliceRestrictionFiberMap p j y ≫
          normalizedCoconeRestrictionFiber (j ≫ p) g (coconePushoutBoundary_eq hp p) y ≫
            vertexFiberι (sliceUnderProjection (f ≫ (i ≫ p))) y := by
  let e := SSet.yonedaEquiv.symm
    (partialColimitSpecifiedCorrectionCosliceEdge hp p c hc dB dC).edge
  let r := normalizedCoconeRestriction (j ≫ p) g (coconePushoutBoundary_eq hp p)
  let a := specifiedCoconeCorrectionFullHomFamily hp p c hc dB dC y
  have hnorm : specifiedCoconeBoundaryCorrectionFullHomFamily hp p c hc dB dC y ≫
        sliceUnderProjection (SSet.yonedaEquiv.symm (intervalFunctorVertexEdge (SSet.yonedaEquiv
          (partialColimitSpanBoundaryPath c hc f (i ≫ p) rfl dB
            g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)).val).val) =
      (a ≫ sliceUnderPostcomp e r) ≫ sliceUnderProjection (e ≫ r) := by
    rw [specifiedCoconeBoundaryCorrectionFullHomFamily, Category.assoc,
      sliceUnder_eqToHom_projection (specifiedCoconeCorrectionCoslice_boundary hp p c hc dB dC)]
  have hmap : (a ≫ sliceUnderPostcomp e r) ≫ sliceUnderProjection (e ≫ r) =
      (a ≫ sliceUnderProjection e) ≫ r := by
    rw [Category.assoc, sliceUnderPostcomp_projection]
    exact (Category.assoc a (sliceUnderProjection e) r).symm
  have hend := congrArg (fun b :
      pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
        sliceUnder (j ≫ p) ↦ b ≫ r)
    (specifiedCoconeCorrectionFullHomFamily_endpoint hp p c hc dB dC y)
  have hfibre := vertexFiberMap_ι (sliceUnderProjection (j ≫ p))
    (sliceUnderProjection (f ≫ (i ≫ p))) r
    (normalizedCoconeRestriction_projection (j ≫ p) g (coconePushoutBoundary_eq hp p)) y
  have hlast := congrArg (fun b : coconeMappingSpace (j ≫ p) y ⟶ sliceUnder (f ≫ (i ≫ p)) ↦
    coconePointHomFamily (partialColimitSpecifiedPathCocone hp p c hc dB dC) y ≫
      cosliceRestrictionFiberMap p j y ≫ b) hfibre.symm
  exact hnorm.trans (hmap.trans (hend.trans
    (by simpa only [Category.assoc, normalizedCoconeRestrictionFiber] using hlast)))

end
end SerrePositivity.InfinityCategories.HomotopyLimits
