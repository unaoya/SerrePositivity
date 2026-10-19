module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeTriangleFamilies
public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativePrefixTetrahedron

/-!
概要：指定右修正三角形に共通部分の始対象からの実際の比較辺を前置する。
方針：共通部分へ制限した三角形を、元の span の右三角形の退化を底として相対的に延長する。
規約：付加比較辺・修正三角形・native な三角形の三単体を厳密に保持する。
使われ方：共通部分の始対象の Hom 比較における三面の整合性。
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

/-- 共通部分へ制限した、同じ指定右修正三角形。 -/
def specifiedCoconeCommonRightTriangle :
    (Δ[2] : SSet.{u + 1}) ⟶ sliceUnder (f ≫ (i ≫ p)) :=
  specifiedCoconeRightTriangle hp p c hc dB dC ≫
    normalizedCoconeRestriction (j ≫ p) g (coconePushoutBoundary_eq hp p)

/-- 共通部分の実際の付加比較辺を前置し、native な右三角形の右退化を底に持つ四面体が存在。 -/
lemma exists_specifiedCoconeRootedRightTetrahedron :
    ∃ s : (Δ[3] : SSet.{u + 1}) ⟶ sliceUnder (f ≫ (i ≫ p)),
      (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ≫ s =
        SSet.yonedaEquiv.symm
          (colimitAttachmentRestrictionEdge c hc g (j ≫ p)
            (coconePushoutBoundary_eq hp p) dC).edge ∧
      stdSimplex.δ (0 : Fin 4) ≫ s = specifiedCoconeCommonRightTriangle hp p c hc dB dC ∧
      s ≫ sliceUnderProjection (f ≫ (i ≫ p)) =
        stdSimplex.σ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm
          (partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
            g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).simplex := by
  let r := normalizedCoconeRestriction (j ≫ p) g (coconePushoutBoundary_eq hp p)
  let e := colimitAttachmentRestrictionEdge c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
  let a := SSet.yonedaEquiv.symm e.edge
  let t := specifiedCoconeRightTriangle hp p c hc dB dC
  let v := SSet.yonedaEquiv.symm (partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).simplex
  have h₂ : stdSimplex.δ (2 : Fin 3) ≫ t =
      SSet.yonedaEquiv.symm (specifiedCoconeBranchData hp p c hc dB dC).transport.edge := by
    dsimp only [t]
    rw [specifiedCoconeRightTriangle, stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm
      (specifiedCoconeBranchData hp p c hc dB dC).triangle.d₂
  have hfirst : (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) ≫ t =
      SSet.yonedaEquiv.symm dC := by
    rw [Category.assoc, h₂,
      (specifiedCoconeBranchData hp p c hc dB dC).transport.δ_one_yonedaEquiv_symm]
  have ha : (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) ≫
      specifiedCoconeCommonRightTriangle hp p c hc dB dC = stdSimplex.δ (0 : Fin 2) ≫ a := by
    have he : stdSimplex.δ (0 : Fin 2) ≫ a = SSet.yonedaEquiv.symm dC ≫ r := by
      rw [e.δ_zero_yonedaEquiv_symm, SSet.yonedaEquiv_symm_comp]
    exact (Category.assoc _ t r).symm.trans
      ((congrArg (fun k ↦ k ≫ r) hfirst).trans he.symm)
  have he : stdSimplex.δ (2 : Fin 3) ≫ v = a ≫ sliceUnderProjection (f ≫ (i ≫ p)) := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    have h := (partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
      g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).d₂
    rw [h, SSet.Edge.ofTruncated_edge]
    exact (colimitAttachmentRestrictionEdge_projection_map c hc g (j ≫ p)
      (coconePushoutBoundary_eq hp p) dC).symm
  have hv : stdSimplex.δ (0 : Fin 3) ≫ v = SSet.yonedaEquiv.symm
      (partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).edge := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm
      (partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).d₀
  have ht : specifiedCoconeCommonRightTriangle hp p c hc dB dC ≫
      sliceUnderProjection (f ≫ (i ≫ p)) =
        stdSimplex.σ (1 : Fin 2) ≫ (stdSimplex.δ (0 : Fin 3) ≫ v) := by
    calc
      _ = t ≫ sliceUnderProjection (j ≫ p) := by
        rw [specifiedCoconeCommonRightTriangle, Category.assoc,
          normalizedCoconeRestriction_projection]
      _ = _ := (specifiedCoconeRightTriangle_base hp p c hc dB dC).trans
        (congrArg (fun k ↦ stdSimplex.σ (1 : Fin 2) ≫ k) hv.symm)
  exact exists_prefixTetrahedron_over_degenerateTriangle
    (sliceUnderProjection (f ≫ (i ≫ p))) a
    (specifiedCoconeCommonRightTriangle hp p c hc dB dC) ha v he ht

/-- 付加比較辺・指定右修正三角形・底の native 三単体を保持する、選んだ同じ四面体。 -/
def specifiedCoconeRootedRightTetrahedron :
    (Δ[3] : SSet.{u + 1}) ⟶ sliceUnder (f ≫ (i ≫ p)) :=
  (exists_specifiedCoconeRootedRightTetrahedron hp p c hc dB dC).choose

/-- 四面体の最初の辺は、元の共通部分の付加比較辺。 -/
lemma specifiedCoconeRootedRightTetrahedron_firstEdge :
    (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ≫
        specifiedCoconeRootedRightTetrahedron hp p c hc dB dC =
      SSet.yonedaEquiv.symm (colimitAttachmentRestrictionEdge c hc g (j ≫ p)
        (coconePushoutBoundary_eq hp p) dC).edge :=
  (exists_specifiedCoconeRootedRightTetrahedron hp p c hc dB dC).choose_spec.1

/-- 四面体の終端面は、同じ指定右修正三角形の共通部分への制限。 -/
lemma specifiedCoconeRootedRightTetrahedron_terminalFace :
    stdSimplex.δ (0 : Fin 4) ≫ specifiedCoconeRootedRightTetrahedron hp p c hc dB dC =
      specifiedCoconeCommonRightTriangle hp p c hc dB dC :=
  (exists_specifiedCoconeRootedRightTetrahedron hp p c hc dB dC).choose_spec.2.1

/-- 四面体の底は、元の native な右三角形の右退化そのもの。 -/
lemma specifiedCoconeRootedRightTetrahedron_base :
    specifiedCoconeRootedRightTetrahedron hp p c hc dB dC ≫
        sliceUnderProjection (f ≫ (i ≫ p)) =
      stdSimplex.σ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm
        (partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
          g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).simplex :=
  (exists_specifiedCoconeRootedRightTetrahedron hp p c hc dB dC).choose_spec.2.2

/-- 四面体の最初の頂点は共通部分の元の始対象。 -/
lemma specifiedCoconeRootedRightTetrahedron_initialVertex :
    (stdSimplex.δ (1 : Fin 2) ≫
        (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4))) ≫
      specifiedCoconeRootedRightTetrahedron hp p c hc dB dC = SSet.yonedaEquiv.symm c := by
  rw [Category.assoc, specifiedCoconeRootedRightTetrahedron_firstEdge,
    (colimitAttachmentRestrictionEdge c hc g (j ≫ p)
      (coconePushoutBoundary_eq hp p) dC).δ_one_yonedaEquiv_symm]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
