module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ArrowIdentityComposition
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SimplicialHomotopyOpposite
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TerminalBoundaryEdgeLift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningEdgeComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeHomotopyEdges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeLeg
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictCoconeLegs
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeExt
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeLegReverse
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitHomotopyPointwise
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseLimitCriterion
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.HomotopyPrecomposition
public import SerrePositivity.InfinityCategories.Sheaves.CechIndexConstantLimit
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsRelativeCech
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsRelativeCechDiagonal

/-!
概要：相対 Čech 図式の元の増大錐と定値錐の間に指定された円柱を作る。
方針：相対終点境界を充填し、各脚の自然性と元の増大・対角の合成で頂点辺を計算する。
  文献対応：HTT 6.2.2.6、Kerodon Proposition 7.1.6.13（Tag 02XD）。
使われ方：像への射に沿う切断の可逆性。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open Truncated.HomotopyCategory

namespace SerrePositivity.InfinityCategories.Sheaves

private theorem conePrism_to_limit {K E : SSet.{u}} [Quasicategory E]
    {F G : K ⟶ E} (c : JoinCone F) (d : JoinCone G) (hd : IsLimitCone d)
    (h : SSet.Homotopy F G) :
    ∃ H : SSet.Homotopy c.val d.val,
      (joinInr (Δ[0] : SSet.{u}) K ▷ Δ[1]) ≫ H.h = h.h := by
  let p := coneRestriction K E
  have hc₀ : p.app _ (functorVertex c.val) = functorVertex F := by
    change functorVertex (joinInr Δ[0] K ≫ c.val) = functorVertex F
    exact congrArg functorVertex c.property
  have hd₀ : p.app _ (functorVertex d.val) = functorVertex G := by
    change functorVertex (joinInr Δ[0] K ≫ d.val) = functorVertex G
    exact congrArg functorVertex d.property
  let e := (SSet.Edge.ofTruncated (functorEdgeOfSimplicialHomotopy h)).ofEq hc₀.symm hd₀.symm
  obtain ⟨a, ha⟩ := exists_edge_lift_of_terminalBoundaryLifting p
    (functorVertex c.val) (functorVertex d.val)
    (terminalBoundaryLifting_coneRestriction_of_isLimitCone d hd) e.toTruncated
  refine ⟨simplicialHomotopyOfFunctorEdge a, ?_⟩
  have he : p.app (Opposite.op ⦋1⦌) a.edge =
      SSet.yonedaEquiv (curry h.h) :=
    congrArg Truncated.Edge.edge ha
  change (joinInr Δ[0] K ▷ Δ[1]) ≫ uncurry (SSet.yonedaEquiv.symm a.edge) = _
  have hp : SSet.yonedaEquiv.symm a.edge ≫ p = curry h.h := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact he
  rw [← uncurry_pre_app]
  change uncurry (SSet.yonedaEquiv.symm a.edge ≫ p) = _
  rw [hp, uncurry_curry]

private theorem relativeCechDiagonal_op_composition {C : Type u} [SmallCategory C]
    {P Q : Cᵒᵖ ⥤ Type u} (g : P ⟶ Q)
    (j : AsSmall.{u} SimplexCategoryᵒᵖ)
    {E : SSet.{u + 1}} (L : (PresheafCat C SpaceInfinity.{u}).op ⟶ E) :
    let I := (discretePresheafInclusion C).val
    let a := edgeOp ((nerve.edgeMk ((relativeCechCocone g).ι.app j)).map I).toTruncated
    let b := edgeOp ((nerve.edgeMk ((relativeCechDiagonal g).app j)).map I).toTruncated
    let c := edgeOp ((nerve.edgeMk g).map I).toTruncated
    homMk (a.map ((truncation 2).map L)) ≫ homMk (b.map ((truncation 2).map L)) =
      homMk (c.map ((truncation 2).map L)) := by
  intro I a b c
  have hg : (relativeCechDiagonal g).app j ≫ (relativeCechCocone g).ι.app j = g :=
    congrArg (fun η ↦ η.app j) (relativeCechDiagonal_cocone g)
  obtain ⟨t⟩ := (nerve.nonempty_compStruct_iff _ _ _).mpr hg
  exact homMk_comp_homMk ((compStructOp (t.map I).toTruncated).map ((truncation 2).map L))

private theorem conePrism_apex_restriction {K E : SSet.{u}}
    {F G : K ⟶ E} {c : JoinCone F} {d : JoinCone G} (H : SSet.Homotopy c.val d.val) :
    ∃ ρ : SSet.Homotopy (SSet.yonedaEquiv.symm c.vertex) (SSet.yonedaEquiv.symm d.vertex),
      (joinInl (Δ[0] : SSet.{u}) K ▷ Δ[1]) ≫ H.h = ρ.h ∧
      Arrow.mk (homMk (simplicialHomotopyVertexEdge ρ
          (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))).toTruncated) =
        Arrow.mk (homMk (coneHomotopyApexEdge H)) := by
  let i := joinInl (Δ[0] : SSet.{u}) K
  let h := stableHomotopyPrecomp i H
  have hc : i ≫ c.val = SSet.yonedaEquiv.symm c.vertex := by
    rw [JoinCone.vertex_eq, Equiv.symm_apply_apply]
  have hd : i ≫ d.val = SSet.yonedaEquiv.symm d.vertex := by
    rw [JoinCone.vertex_eq, Equiv.symm_apply_apply]
  let ρ : SSet.Homotopy (SSet.yonedaEquiv.symm c.vertex) (SSet.yonedaEquiv.symm d.vertex) :=
    { h := h.h
      h₀ := h.h₀.trans hc
      h₁ := h.h₁.trans hd
      rel := h.rel }
  refine ⟨ρ, rfl, congr_arrowMk_homMk _ _ ?_⟩
  exact homotopyVertexEdge_precomp i H (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))

private theorem discreteRelativeCechCocone_leg_simplex {C : Type u} [SmallCategory C]
    {P Q : Cᵒᵖ ⥤ Type u} (g : P ⟶ Q) (j : AsSmall.{u} SimplexCategoryᵒᵖ) :
    (discretePresheafCocone (relativeCechCocone g)).val.app (Opposite.op ⦋1⦌)
      (joinCoconeLegSimplex (ULift.up (nerveVertex j))) =
    ((nerve.edgeMk ((relativeCechCocone g).ι.app j)).map (kanDiscretePresheafMap C)).edge := by
  let J := AsSmall.{u} SimplexCategoryᵒᵖ
  let K := (SSet.uliftFunctor.{u + 1, u}).obj (nerve J)
  let v : K _⦋0⦌ := ULift.up (nerveVertex j)
  let w := (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌) : (Δ[0] : SSet.{u + 1}) _⦋0⦌)
  let p := SSet.yonedaEquiv.symm v
  have h₁ : SSet.yonedaEquiv ((pointJoinStdSimplexIso.{u + 1} 0).inv) =
      joinCoconeLegSimplex w := by
    have h := congrArg (fun x ↦ (pointJoinStdSimplexIso.{u + 1} 0).inv.app
      (Opposite.op ⦋1⦌) x) pointJoinStdSimplexIso_zero_leg
    have h' : (pointJoinStdSimplexIso.{u + 1} 0).inv.app (Opposite.op ⦋1⦌)
        ((pointJoinStdSimplexIso.{u + 1} 0).hom.app (Opposite.op ⦋1⦌)
          (joinCoconeLegSimplex w)) = joinCoconeLegSimplex w := by
      exact ConcreteCategory.congr_hom
        (NatTrans.congr_app (pointJoinStdSimplexIso.{u + 1} 0).hom_inv_id
          (Opposite.op ⦋1⦌)) _
    exact h.symm.trans h'
  have h₂ : p.app (Opposite.op ⦋0⦌) w = v := by
    change SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u + 1}) ≫ p) = v
    rw [Category.id_comp, Equiv.apply_symm_apply]
  let c := (kanDiscretePresheafFunctor C).mapCocone (relativeCechCocone g)
  have ht := congrArg (fun k ↦ SSet.yonedaEquiv (k ≫ kanDiagramRealization Cᵒᵖ))
    (strictNativeCoconeLeg_eq c j)
  change SSet.yonedaEquiv ((coherentCoconeLegMap
    (SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone c) p) ≫
      kanDiagramRealization Cᵒᵖ) = _ at ht
  simp only [coherentCoconeLegMap, ← Category.assoc, SSet.yonedaEquiv_comp] at ht
  rw [h₁, joinCoconeLegSimplex_natural, h₂] at ht
  rw [kanDiscretePresheafMap]
  change _ = (kanDiagramRealization Cᵒᵖ).app (Opposite.op ⦋1⦌)
    ((SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent
      (KanDiagramObject Cᵒᵖ)).app (Opposite.op ⦋1⦌)
      ((nerveMap (kanDiscretePresheafFunctor C)).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ ((relativeCechCocone g).ι.app j))))
  rw [nerveMap_app_mk₁]
  exact ht.trans (congrArg ((kanDiagramRealization Cᵒᵖ).app (Opposite.op ⦋1⦌))
    (SSet.yonedaEquiv.apply_symm_apply _))

private theorem evaluateHomotopy_cast_target {A E : SSet.{u}} {F G G' : A ⟶ E}
    (h : G = G') (H : SSet.Homotopy F G) (a : FunctorHom F G')
    (ha : HEq a (homMk (functorEdgeOfSimplicialHomotopy H))) (k : A _⦋0⦌) :
    Arrow.mk (functorHomEvaluate a k) =
      Arrow.mk (homMk (simplicialHomotopyVertexEdge H k).toTruncated) := by
  subst G'
  have ha' := eq_of_heq ha
  rw [ha', functorHomEvaluate_homotopy]

private theorem weightedSectionsRelativeCechDiagonal_component {C : Type u} [SmallCategory C]
    {P Q : Cᵒᵖ ⥤ Type u} (g : P ⟶ Q) (j : AsSmall.{u} SimplexCategoryᵒᵖ)
    {E : SSet.{u + 1}} [Quasicategory E] (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    let L := SerrePositivity.InfinityCategories.Sheaves.weightedSections O hE
    let k : cechReverseIndex.{u} _⦋0⦌ := SSet.opObjEquiv.symm (ULift.up (nerveVertex j))
    let I := (discretePresheafInclusion C).val
    let b := edgeOp ((nerve.edgeMk ((relativeCechDiagonal g).app j)).map I).toTruncated
    Arrow.mk (functorHomEvaluate (weightedSections_relativeCechDiagonalHom g O hE) k) =
      Arrow.mk (homMk (b.map ((truncation 2).map L))) := by
  intro L k I b
  let t := discreteRelativeCechDiagonalHomotopy g
  let H := functorHomotopyPostcomp (homotopyOpposite t) L
  have ht : SSet.opFunctor.map (SSet.const (X := ((SSet.uliftFunctor.{u + 1, u}).obj
      (nerve (AsSmall.{u} SimplexCategoryᵒᵖ)))) (functorVertex (discretePresheaf P))) ≫ L =
      (SSet.const
      (L.app _ (opObjEquiv.symm (functorVertex (discretePresheaf P)))) : cechReverseIndex.{u} ⟶ E) := by
    change (SSet.const (SSet.opObjEquiv.symm
      (functorVertex (discretePresheaf P))) : cechReverseIndex.{u} ⟶ _) ≫ L = _
    rw [SSet.const_comp]
  have he : HEq (weightedSections_relativeCechDiagonalHom g O hE)
      (homMk (functorEdgeOfSimplicialHomotopy H)) := by
    unfold weightedSections_relativeCechDiagonalHom
    exact cast_heq _ _
  have h₀ := evaluateHomotopy_cast_target ht H _ he k
  refine h₀.trans (congr_arrowMk_homMk _ _ ?_)
  have hv := kanHomotopyOpposite_vertex_edge t (ULift.up (nerveVertex j))
  change L.app (Opposite.op ⦋1⦌)
    (simplicialHomotopyVertexEdge (homotopyOpposite t) k).edge =
      L.app (Opposite.op ⦋1⦌) b.edge
  apply congrArg (L.app (Opposite.op ⦋1⦌))
  change (simplicialHomotopyVertexEdge (homotopyOpposite t) k).edge =
    SSet.opObjEquiv.symm (((nerve.edgeMk ((relativeCechDiagonal g).app j)).map I).edge)
  exact hv.trans (congrArg SSet.opObjEquiv.symm
    (discreteRelativeCechDiagonalHomotopy_component g j))

private theorem nativeConeLeg_simplex {K E : SSet.{u}} {F : K ⟶ E}
    (A : JoinCone F) (x : K _⦋0⦌) :
    (nativeConeLeg A x).edge = A.val.app (Opposite.op ⦋1⦌) (joinConeLegSimplex x) := by
  let w := (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌) : (Δ[0] : SSet.{u}) _⦋0⦌)
  let p := SSet.yonedaEquiv.symm x
  have h₁ : SSet.yonedaEquiv ((pointJoinStdSimplexIso.{u} 0).inv) =
      joinConeLegSimplex w := by
    have h := congrArg (fun y ↦ (pointJoinStdSimplexIso.{u} 0).inv.app
      (Opposite.op ⦋1⦌) y) pointJoinStdSimplexIso_zero_leg
    have h' : (pointJoinStdSimplexIso.{u} 0).inv.app (Opposite.op ⦋1⦌)
        ((pointJoinStdSimplexIso.{u} 0).hom.app (Opposite.op ⦋1⦌)
          (joinConeLegSimplex w)) = joinConeLegSimplex w := by
      exact ConcreteCategory.congr_hom
        (NatTrans.congr_app (pointJoinStdSimplexIso.{u} 0).hom_inv_id (Opposite.op ⦋1⦌)) _
    exact h.symm.trans h'
  have h₂ : p.app (Opposite.op ⦋0⦌) w = x := by
    change SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}) ≫ p) = x
    rw [Category.id_comp, Equiv.apply_symm_apply]
  change SSet.yonedaEquiv
      ((pointJoinStdSimplexIso.{u} 0).inv ≫ joinMap (𝟙 Δ[0]) p ≫ A.val) = _
  rw [← Category.assoc, SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp,
    h₁, joinConeLegSimplex_natural, h₂]

private theorem coneHomotopyDiagramEdge_simplex {K E : SSet.{u}}
    {F G : K ⟶ E} (A : JoinCone F) (d : JoinCone G)
    (H : SSet.Homotopy A.val d.val) (h : SSet.Homotopy F G)
    (hD : (joinInr (Δ[0] : SSet.{u}) K ▷ Δ[1]) ≫ H.h = h.h) (k : K _⦋0⦌) :
    (coneHomotopyDiagramEdge H k).edge = (simplicialHomotopyVertexEdge h k).edge := by
  have he := homotopyVertexEdge_precomp (joinInr (Δ[0] : SSet.{u}) K) H k
  let x := ((Truncated.Edge.id (X := (truncation 2).obj K) k).edge,
    homotopyIntervalEdge.edge)
  change ((joinInr (Δ[0] : SSet.{u}) K ▷ Δ[1]) ≫ H.h).app (Opposite.op ⦋1⦌) x =
    (coneHomotopyDiagramEdge H k).edge at he
  rw [hD] at he
  exact he.symm

private theorem heq_of_arrowMk {D : Type*} [Category* D]
    {a b x y : D} {f : a ⟶ b} {g : x ⟶ y} (h : Arrow.mk f = Arrow.mk g) : HEq f g := by
  obtain ⟨rfl, rfl, hh⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id, heq_iff_eq] using hh

/-- 指定した Čech 増大と定値錐を結ぶ円柱は、図式面と元の像への射の類を保持する。 -/
@[cite HTT "6.2.2.6" (partial := special) "小さい通常の site の集合値 Čech 解消の指定比較。"]
lemma weightedSections_toRange_conePrism :
∀ {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E],
∀ {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q)
 (O : Presheaf C E) (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E),
let g := Subfunctor.toRange f
let A := mapJoinCone (SerrePositivity.InfinityCategories.Sheaves.weightedSections O hE)
 (coconeReverseCone (discretePresheafCocone (relativeCechCocone g)))
let z := (SerrePositivity.InfinityCategories.Sheaves.weightedSections O hE).app _ (opObjEquiv.symm (functorVertex (discretePresheaf P)))
let d := constantDiagramCone cechReverseIndex.{u} E z
∃ (H : join (Δ[0] : SSet.{u + 1}) cechReverseIndex.{u} ⊗ Δ[1] ⟶ E)
 (ρ : SSet.Homotopy (SSet.yonedaEquiv.symm A.vertex)
   (SSet.yonedaEquiv.symm d.vertex)),
 SSet.ι₀ ≫ H = A.val ∧ SSet.ι₁ ≫ H = d.val ∧
 (joinInr (Δ[0] : SSet.{u + 1}) cechReverseIndex.{u} ▷ Δ[1]) ≫ H =
   (functorHomHomotopy (weightedSections_relativeCechDiagonalHom g O hE)).h ∧
 (joinInl (Δ[0] : SSet.{u + 1}) cechReverseIndex.{u} ▷ Δ[1]) ≫ H = ρ.h ∧
 HEq (Truncated.HomotopyCategory.homMk
   (simplicialHomotopyVertexEdge ρ (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))).toTruncated)
 (Truncated.HomotopyCategory.homMk
   ((edgeOp (((nerve.edgeMk g).map (discretePresheafInclusion C).val).toTruncated)).map
     ((truncation 2).map (SerrePositivity.InfinityCategories.Sheaves.weightedSections O hE)))) := by
  intro C hC E hE₀ P Q f O hE g A z d
  let L := SerrePositivity.InfinityCategories.Sheaves.weightedSections O hE
  let I := (discretePresheafInclusion C).val
  let J := AsSmall.{u} SimplexCategoryᵒᵖ
  let j : J := AsSmall.up.obj (Opposite.op ⦋0⦌)
  let k : cechReverseIndex.{u} _⦋0⦌ := SSet.opObjEquiv.symm (ULift.up (nerveVertex j))
  let h := functorHomHomotopy (weightedSections_relativeCechDiagonalHom g O hE)
  obtain ⟨H, hD⟩ := conePrism_to_limit A d (cechConstantCone_isLimit E z) h
  obtain ⟨ρ, hρ, hApex⟩ := conePrism_apex_restriction H
  refine ⟨H.h, ρ, H.h₀, H.h₁, hD, hρ, ?_⟩
  let a := edgeOp ((nerve.edgeMk ((relativeCechCocone g).ι.app j)).map I).toTruncated
  let b := edgeOp ((nerve.edgeMk ((relativeCechDiagonal g).app j)).map I).toTruncated
  let e := edgeOp ((nerve.edgeMk g).map I).toTruncated
  have hLeg : Arrow.mk (homMk (nativeConeLeg A k)) =
      Arrow.mk (homMk (a.map ((truncation 2).map L))) := by
    apply congr_arrowMk_homMk
    rw [nativeConeLeg_simplex]
    change L.app (Opposite.op ⦋1⦌)
      ((coconeReverseCone (discretePresheafCocone (relativeCechCocone g))).val.app
        (Opposite.op ⦋1⦌) (joinConeLegSimplex k)) = _
    rw [coconeReverseCone_leg, discreteRelativeCechCocone_leg_simplex]
    rfl
  have hDiag : Arrow.mk (homMk (coneHomotopyDiagramEdge H k)) =
      Arrow.mk (homMk (b.map ((truncation 2).map L))) := by
    have hi := congr_arrowMk_homMk (coneHomotopyDiagramEdge H k)
      (simplicialHomotopyVertexEdge h k).toTruncated (coneHomotopyDiagramEdge_simplex A d H h hD k)
    exact hi.trans ((congrArg Arrow.mk (functorHomHomotopy_component
      (weightedSections_relativeCechDiagonalHom g O hE) k)).trans
        (weightedSectionsRelativeCechDiagonal_component g j O hE))
  have hOne : Arrow.mk (homMk (nativeConeLeg d k)) = Arrow.mk (𝟙 (HomotopyCategory.mk z)) := by
    let i : E.Edge z z := SSet.Edge.id z
    have hi : Arrow.mk (homMk (nativeConeLeg d k)) = Arrow.mk (homMk i.toTruncated) := by
      apply congr_arrowMk_homMk
      change SSet.yonedaEquiv (coneLegInclusion k ≫ SSet.const z) = _
      rw [SSet.comp_const]
      exact pinchedConstant_one z
    exact hi.trans (congrArg Arrow.mk (SSet.HomotopyCategory.homMk_id z))
  have hNat := congrArg Arrow.mk (coneHomotopy_leg_naturality H k)
  have hComp := arrowMk_comp_congr _ _ _ _ hLeg hDiag
  have hRight := arrowMk_comp_of_right_identity (homMk (coneHomotopyApexEdge H))
    (homMk (nativeConeLeg d k)) hOne
  have hEq := hApex.trans (hRight.symm.trans (hNat.symm.trans (hComp.trans
    (congrArg Arrow.mk (relativeCechDiagonal_op_composition g j L)))))
  exact heq_of_arrowMk hEq

end SerrePositivity.InfinityCategories.Sheaves
