module

public import SerrePositivity.InfinityCategories.F2.Tensor.SetSectionsNaturality
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictCones
public import SerrePositivity.InfinityCategories.Core.UniverseLimits
public import SerrePositivity.InfinityCategories.F1B.FilteredExchange.ConeRestrictionTransport

/-!
概要：篩包含の G8 自然性に使う、表現可能前層の評価錐。
方針：要素の圏の始対象 (U, 𝟙) から明示した錐を作り、篩の要素の圏へ制限する。
規約：任意の篩と任意の前層を扱う。位相・被覆条件・層条件は使わない。
この段階では G8 の四角形そのものは未証明。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits
namespace SetWeight

variable {C : Type u} [SmallCategory C] (U : C)

/-- 表現可能前層の要素の圏の始対象から射影への明示的な錐。 -/
def representableProjectionCone : JoinCone (projection (yoneda.obj U)) :=
  ⟨nerveInitialCone (Functor.Elements.isInitialYonedaObj U) ≫ projection (yoneda.obj U), by
    rw [← Category.assoc, nerveInitialCone_inr, Category.id_comp]⟩

/-- この錐の頂点は底の U そのもの。 -/
lemma representableProjectionCone_vertex :
    (representableProjectionCone U).vertex = nerveVertex (Opposite.op U) := by
  rw [JoinCone.vertex_eq]
  change SSet.yonedaEquiv (joinInl Δ[0] _ ≫
    (nerveInitialCone (Functor.Elements.isInitialYonedaObj U) ≫
      projection (yoneda.obj U))) = _
  rw [← Category.assoc, nerveInitialCone_left, SSet.yonedaEquiv_comp]
  rfl

variable {E : SSet.{u + 1}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve Cᵒᵖ) ⟶ E)

/-- 任意の前層 F の U での値から、表現可能前層の要素の図式へ向かう錐。 -/
def representableEvaluationCone : JoinCone (diagram (yoneda.obj U) F) :=
  mapJoinCone F (JoinCone.ulift.{u, u + 1} (representableProjectionCone U))

/-- 評価錐の頂点は F(U)。同値による同定ではなく頂点の等式。 -/
lemma representableEvaluationCone_vertex :
    (representableEvaluationCone U F).vertex =
      F.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Opposite.op U))) := by
  rw [representableEvaluationCone, mapJoinCone_vertex, JoinCone.ulift_vertex,
    representableProjectionCone_vertex]

variable {U} (S : Sieve U)

/-- F(U) の評価錐を篩の要素へ制限する。同じ包含関手を厳密に使う。 -/
def sieveEvaluationCone : JoinCone (diagram S.functor F) :=
  restrictSectionsCone S.functorInclusion F (representableEvaluationCone U F)

/-- 篩への制限後も頂点は F(U)。 -/
lemma sieveEvaluationCone_vertex :
    (sieveEvaluationCone F S).vertex =
      F.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Opposite.op U))) := by
  rw [sieveEvaluationCone, restrictSectionsCone_vertex, representableEvaluationCone_vertex]

/-- 明示的な評価錐から、指定された表現可能側の極限錐への普遍辺。 -/
def representableEvaluationConeMap (cU : JoinCone (diagram (yoneda.obj U) F))
    (hcU : IsLimitCone cU) :
    SSet.Edge (X := sliceOver (diagram (yoneda.obj U) F))
      (representableEvaluationCone U F) cU :=
  SSet.Edge.ofTruncated (Classical.choice
    ((show IsTerminalVertex (X := sliceOver (diagram (yoneda.obj U) F)) cU from hcU
      ).nonempty_edge (representableEvaluationCone U F)))

/-- 篩へ制限した評価錐から、指定された篩側の極限錐への普遍辺。 -/
def sieveEvaluationConeMap (cS : JoinCone (diagram S.functor F))
    (hcS : IsLimitCone cS) :
    SSet.Edge (X := sliceOver (diagram S.functor F)) (sieveEvaluationCone F S) cS :=
  sectionsConeMap S.functorInclusion F cS hcS (representableEvaluationCone U F)

/-- 篩の要素への制限を、錐の圏全体の射として使う。 -/
def sieveConeRestriction :
    sliceOver (diagram (yoneda.obj U) F) ⟶ sliceOver (diagram S.functor F) :=
  F2.normalizedConeRestriction (diagram (yoneda.obj U) F)
    (elementsMap S.functorInclusion) (elementsMap_diagram S.functorInclusion F)

/-- 錐の圏の制限は、先行 API の指定錐の制限に一致する。 -/
lemma sieveConeRestriction_cone (c : JoinCone (diagram (yoneda.obj U) F)) :
    (sieveConeRestriction F S).app (Opposite.op ⦋0⦌) c =
      restrictSectionsCone S.functorInclusion F c := by
  have transport {K : SSet.{u + 1}} {p q : K ⟶ E} (h : p = q) (d : JoinCone p) :
      (eqToHom (congrArg sliceOver h)).app (Opposite.op ⦋0⦌) d =
        (⟨d.val, d.property.trans h⟩ : JoinCone q) := by
    cases h
    rfl
  exact transport (elementsMap_diagram S.functorInclusion F)
    (restrictJoinCone c (elementsMap S.functorInclusion))

/-- 錐の圏での制限は頂点への射影を厳密に保つ。 -/
lemma sieveConeRestriction_projection :
    sieveConeRestriction F S ≫ sliceOverProjection (diagram S.functor F) =
      sliceOverProjection (diagram (yoneda.obj U) F) :=
  F2.normalizedConeRestriction_projection (diagram (yoneda.obj U) F)
    (elementsMap S.functorInclusion) (elementsMap_diagram S.functorInclusion F)

/-- 錐の比較辺を、同じ篩の要素へ制限する。 -/
def sieveRestrictConeEdge {c d : JoinCone (diagram (yoneda.obj U) F)}
    (e : SSet.Edge (X := sliceOver (diagram (yoneda.obj U) F)) c d) :
    SSet.Edge (X := sliceOver (diagram S.functor F))
      (restrictSectionsCone S.functorInclusion F c)
      (restrictSectionsCone S.functorInclusion F d) :=
  (e.map (sieveConeRestriction F S)).ofEq
    (sieveConeRestriction_cone F S c) (sieveConeRestriction_cone F S d)

/-- 評価錐から篩側の極限への普遍辺は、表現可能側の極限を経由しても同じ類。
一意性は篩側の錐の圏で使い、頂点へ射影する前に示す。 -/
lemma sieveEvaluationConeMap_factor [Quasicategory E]
    (cS : JoinCone (diagram S.functor F)) (hcS : IsLimitCone cS)
    (cU : JoinCone (diagram (yoneda.obj U) F)) (hcU : IsLimitCone cU) :
    Truncated.HomotopyCategory.homMk
        (sieveRestrictConeEdge F S (representableEvaluationConeMap F cU hcU)).toTruncated ≫
      Truncated.HomotopyCategory.homMk
        (sectionsConeMap S.functorInclusion F cS hcS cU).toTruncated =
    Truncated.HomotopyCategory.homMk (sieveEvaluationConeMap F S cS hcS).toTruncated :=
  (show IsTerminalVertex (X := sliceOver (diagram S.functor F)) cS from hcS
    ).isTerminalHo.hom_ext _ _

/-- 上の錐の普遍辺の一意性を、任意の M からの全写像空間へ移す。
G8 の比較との照合前に使う、評価錐と指定極限錐の側の全パラメータ比較。 -/
def sieveEvaluationConeMap_postcomposeIso [Quasicategory E]
    (M : E _⦋0⦌)
    (cS : JoinCone (diagram S.functor F)) (hcS : IsLimitCone cS)
    (cU : JoinCone (diagram (yoneda.obj U) F)) (hcU : IsLimitCone cU) :
    FunctorIso
      (PinchedInterval.postcompose M (Truncated.HomotopyCategory.homMk
        ((sieveRestrictConeEdge F S (representableEvaluationConeMap F cU hcU)).map
          (sliceOverProjection (diagram S.functor F))).toTruncated) ≫
       PinchedInterval.postcompose M (Truncated.HomotopyCategory.homMk
        ((sectionsConeMap S.functorInclusion F cS hcS cU).map
          (sliceOverProjection (diagram S.functor F))).toTruncated))
      (PinchedInterval.postcompose M (Truncated.HomotopyCategory.homMk
        ((sieveEvaluationConeMap F S cS hcS).map
          (sliceOverProjection (diagram S.functor F))).toTruncated)) := by
  have h := congrArg
    (fun f => (hoFunctor.map (sliceOverProjection (diagram S.functor F))).toFunctor.map f)
    (sieveEvaluationConeMap_factor F S cS hcS cU hcU)
  rw [Functor.map_comp] at h
  exact PinchedInterval.postcomposeCompIso M _ _ ≪≫
    eqToIso (congrArg (fun f => HomotopyCategory.mk
      (functorVertex (PinchedInterval.postcompose M f))) h)

/-- 表現可能側の評価 F(U) から指定極限への普遍射。 -/
def representableEvaluationMap (cU : JoinCone (diagram (yoneda.obj U) F))
    (hcU : IsLimitCone cU) :
    SSet.Edge (F.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Opposite.op U)))) cU.vertex :=
  ((representableEvaluationConeMap F cU hcU).map
    (sliceOverProjection (diagram (yoneda.obj U) F))).ofEq
      (representableEvaluationCone_vertex U F) rfl

/-- 篩へ制限した評価 F(U) から指定極限への普遍射。 -/
def sieveEvaluationMap (cS : JoinCone (diagram S.functor F))
    (hcS : IsLimitCone cS) :
    SSet.Edge (F.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Opposite.op U)))) cS.vertex :=
  ((sieveEvaluationConeMap F S cS hcS).map
    (sliceOverProjection (diagram S.functor F))).ofEq
      (sieveEvaluationCone_vertex F S) rfl

/-- 始点の頂点表示を正規化しても、切断制限の元の一次単体は変わらない。 -/
lemma sieveSectionsMap_edge (cS : JoinCone (diagram S.functor F)) (hcS : IsLimitCone cS)
    (cU : JoinCone (diagram (yoneda.obj U) F)) (hcU : IsLimitCone cU) :
    (sieveSectionsMap S F cS hcS cU hcU).edge =
      ((sectionsConeMap S.functorInclusion F cS hcS cU).map
        (sliceOverProjection (diagram S.functor F))).edge := by
  have transport {a a' b : E _⦋0⦌} (h : a = a') (e : SSet.Edge a b) :
      (Eq.mp (congrArg (fun t => SSet.Edge t b) h) e).edge = e.edge := by
    cases h
    rfl
  exact transport (restrictSectionsCone_vertex S.functorInclusion F cU)
    ((sectionsConeMap S.functorInclusion F cS hcS cU).map
      (sliceOverProjection (diagram S.functor F)))

/-- F(U) からの二つの普遍射と、指定された sieveSectionsMap の可換三角形。 -/
def sieveEvaluationTriangle [Quasicategory E]
    (cS : JoinCone (diagram S.functor F)) (hcS : IsLimitCone cS)
    (cU : JoinCone (diagram (yoneda.obj U) F)) (hcU : IsLimitCone cU) :
    SSet.Edge.CompStruct (representableEvaluationMap F cU hcU)
      (sieveSectionsMap S F cS hcS cU hcU) (sieveEvaluationMap F S cS hcS) := by
  obtain ⟨t⟩ := compStruct_nonempty_of_homMk_fac
    (sieveEvaluationConeMap_factor F S cS hcS cU hcU)
  let t' := (SSet.Edge.CompStruct.ofTruncated t).map
    (sliceOverProjection (diagram S.functor F))
  apply t'.ofEq
  · change (sieveConeRestriction F S ≫ sliceOverProjection (diagram S.functor F)).app
      (Opposite.op ⦋1⦌) (representableEvaluationConeMap F cU hcU).edge = _
    rw [sieveConeRestriction_projection]
    rfl
  · exact (sieveSectionsMap_edge F S cS hcS cU hcU).symm
  · rfl

/-- 評価からの二経路は、指定された切断制限の後合成を含む全写像空間で同型。 -/
def sieveEvaluation_postcomposeIso [Quasicategory E] (M : E _⦋0⦌)
    (cS : JoinCone (diagram S.functor F)) (hcS : IsLimitCone cS)
    (cU : JoinCone (diagram (yoneda.obj U) F)) (hcU : IsLimitCone cU) :
    FunctorIso
      (PinchedInterval.postcompose M (Truncated.HomotopyCategory.homMk
          (representableEvaluationMap F cU hcU).toTruncated) ≫
        PinchedInterval.postcompose M (Truncated.HomotopyCategory.homMk
          (sieveSectionsMap S F cS hcS cU hcU).toTruncated))
      (PinchedInterval.postcompose M (Truncated.HomotopyCategory.homMk
        (sieveEvaluationMap F S cS hcS).toTruncated)) :=
  PinchedInterval.postcomposeCompIso M _ _ ≪≫
    eqToIso (congrArg (fun f => HomotopyCategory.mk
      (functorVertex (PinchedInterval.postcompose M f)))
        (Truncated.HomotopyCategory.homMk_comp_homMk
          (sieveEvaluationTriangle F S cS hcS cU hcU).toTruncated))

end SetWeight
end SerrePositivity.InfinityCategories
