module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceContractibleColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceInitial
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceProjection
public import SerrePositivity.InfinityCategories.F2.Ind.FiniteColimitPreservationGeneration
public import SerrePositivity.InfinityCategories.F1.Simplicial.FiniteHornUniverseIso
public import SerrePositivity.InfinityCategories.F1.Joins.PointConeSpanIso
public import SerrePositivity.InfinityCategories.Stable.RelativeInitialEndpoint

/-!
概要：固定始域の閉包内射圏の全有限余極限と、包含による指定余錐の保存。
方針：元の恒等射を空図式の余極限とし、標準 span は弱可縮な nerve の計算から移す。
規約：大宇宙の任意の有限単体集合を形状に許す。
使われ方：HTT 5.5.5.11 の小余完備性へ向かう有限工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits

private def emptyCosliceIso {X : SSet.{u}} (T : SSet.{u})
    (p : (⊥ : T.Subcomplex).toSSet ⟶ X) : sliceUnder p ≅ X := by
  let F : X ⟶ sliceUnder p :=
    sliceUnderCurry (emptyJoinIso T X).hom (Subcomplex.isInitialBot.hom_ext _ _)
  have hF : F ≫ sliceUnderProjection p = 𝟙 X := by
    rw [sliceUnderCurry_projection, ← emptyJoinIso_inv, Iso.inv_hom_id]
  refine ⟨sliceUnderProjection p, F, ?_, hF⟩
  apply sliceUnder_empty_hom_ext p
  rw [Category.assoc, hF, Category.comp_id, Category.id_comp]

private lemma hasPreservedEmptyColimit_of_initial {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (U : X ⟶ Y)
    (x : X _⦋0⦌) (hx : IsInitialVertex x) (hUx : IsInitialVertex (U.app _ x))
    (T : SSet.{u}) (p : (⊥ : T.Subcomplex).toSSet ⟶ X) :
    Ind.HasPreservedColimit U p := by
  let e := emptyCosliceIso T p
  let c : JoinCocone p := e.inv.app (Opposite.op ⦋0⦌) x
  have hc : IsColimitCone c := (qCatEquivalenceOfIso e.symm).map_isInitialVertex hx
  have hv : c.vertex = x := by
    change ((e.inv ≫ e.hom).app (Opposite.op ⦋0⦌)) x = x
    rw [e.inv_hom_id]
    rfl
  refine ⟨c, hc, ?_⟩
  apply ((qCatEquivalenceOfIso (emptyCosliceIso T (p ≫ U))).isInitialVertex_iff _).mpr
  change IsInitialVertex (U.app _ c.vertex)
  rwa [hv]

variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 固定始域圏の有限全図式には、全 coslice に保存される余極限がある。 -/
lemma generatedSource_hasPreservedFiniteColimit (hC : HasSmallColimits C)
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (K : SSet.{u + 1}) [K.Finite] (D : K ⟶ generatedSourceCategory edges x) :
    Ind.HasPreservedColimit (generatedSourceInclusion edges x) D := by
  let U := generatedSourceInclusion edges x
  apply Ind.hasPreservedColimit_finite_of_empty_pointSpan U ?_ ?_ K D
  · exact hasPreservedEmptyColimit_of_initial U (generatedSourceIdentity edges x)
      (generatedSourceIdentity_isInitial edges x) (cosliceIdentityCone_isInitialVertex x)
  · intro p
    let e := uliftFiniteSpanNerveIso.{u, u + 1} ≪≫ pointConeSpanIso.symm
    apply (Ind.hasPreservedColimit_iff_restrict_isIso U p e.hom).mpr
    let z : FiniteSpanIndex.{u} := ULift.up FiniteSpanVertex.zero
    have hz : IsInitial z := IsInitial.ofUniqueHom
      (fun _ ↦ homOfLE (Or.inl rfl)) (fun _ _ ↦ Subsingleton.elim _ _)
    have hpoint : IsContractibleKan (Δ[0] : SSet.{u}) := by
      intro n b
      exact ⟨stdSimplex.isTerminalObj₀.from _, stdSimplex.isTerminalObj₀.hom_ext _ _⟩
    have hJ := (nervePoint_isLeftCofinal hz).isWeakHomotopyEquivalence
      |>.weaklyContractible_iff.mp hpoint.isWeaklyContractible
    exact generatedSource_hasNerveColimit hC edges x FiniteSpanIndex hJ (e.hom ≫ p)

/-- 同じ固定始域圏は、元の大宇宙の全有限余極限を持つ。 -/
lemma generatedSource_hasFiniteColimits (hC : HasSmallColimits C)
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌) : HasFiniteColimits (generatedSourceCategory edges x) := by
  constructor
  intro K hK D
  obtain ⟨c, hc, _⟩ := generatedSource_hasPreservedFiniteColimit hC edges x K D
  exact ⟨c, hc⟩

/-- 元の全 coslice への包含は、任意の指定有限余極限余錐を保存する。 -/
lemma generatedSourceInclusion_preservesFiniteColimit (hC : HasSmallColimits C)
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (K : SSet.{u + 1}) [K.Finite] (D : K ⟶ generatedSourceCategory edges x)
    (c : JoinCocone D) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone (generatedSourceInclusion edges x) c) :=
  (generatedSource_hasPreservedFiniteColimit hC edges x K D).map_isColimit c hc

/-- 周囲の全 coslice の任意の指定有限余極限も、同じ閉包内に留まる。 -/
lemma generatedSource_finite_colimit_mem (hC : HasSmallColimits C)
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (K : SSet.{u + 1}) [K.Finite] (D : K ⟶ generatedSourceCategory edges x)
    (c : JoinCocone (D ≫ generatedSourceInclusion edges x)) (hc : IsColimitCone c) :
    (JoinCocone.leg c.vertex (𝟙 Δ[0])).edge ∈ generatedEdges edges := by
  obtain ⟨d, hd, hUd⟩ := generatedSource_hasPreservedFiniteColimit hC edges x K D
  have hm : (JoinCocone.leg (mapJoinCocone (generatedSourceInclusion edges x) d).vertex
      (𝟙 Δ[0])).edge ∈ generatedEdges edges := by
    rw [Ind.mapJoinCocone_vertex]
    exact fullSubcomplexOnVertices_vertex d.vertex
  exact (generatedSourceCondition_iff_vertexIso edges x
    (colimitVertexIso (mapJoinCocone (generatedSourceInclusion edges x) d) c hUd hc)).mp hm

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
