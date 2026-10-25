module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceFiberPullback
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullSubcomplexRestrictionEquivalence

/-!
概要：閉包内射の固定始域 coslice と、飽和射圏の厳密な始点 fiber を同値にする。
方針：厳密な fiber を周囲の fiber の全部分圏として表示し、公開の制限同値を使う。
規約：同じ全比較を保持する。presentable 性・終対象の存在はこの同値から単独では主張しない。
使われ方：固定始域圏の accessibility と余完備性の次工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 周囲の始点 fiber 内で、元の射が生成閉包に入る頂点条件。 -/
def sourceArrowFiberCondition (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (f : (vertexFiber (evaluateFunctorAt (Y := C)
      (stdSimplex.obj₀Equiv.symm 0 : Δ[1] _⦋0⦌)) x) _⦋0⦌) : Prop :=
  arrowVertexEdge f.val ∈ generatedEdges edges

/-- 厳密な閉包内射 fiber は、周囲の同じ fiber の元の全部分圏と同型。 -/
def generatedSourceArrowFullFiberIso (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    generatedSourceArrowFiber edges x ≅
      (fullSubcomplexOnVertices (vertexFiber (evaluateFunctorAt (Y := C)
        (stdSimplex.obj₀Equiv.symm 0 : Δ[1] _⦋0⦌)) x) (sourceArrowFiberCondition edges x)) := by
  let Q := sourceArrowFiberCondition edges x
  let j := (fullSubcomplexOnVertices _ Q).ι
  let v := vertexFiberι (evaluateFunctorAt (Y := C)
    (stdSimplex.obj₀Equiv.symm 0 : Δ[1] _⦋0⦌)) x
  let w := vertexFiberι (generatedArrowInclusion edges ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)) x
  let H := fullSubcomplexLift Q (generatedSourceArrowFiberInclusion edges x)
    (fun t ↦ fullSubcomplexOnVertices_vertex t.val)
  have hH : H ≫ j = generatedSourceArrowFiberInclusion edges x :=
  fullSubcomplexLift_ι _ _
    (fun t : (generatedSourceArrowFiber edges x) _⦋0⦌ ↦ fullSubcomplexOnVertices_vertex t.val)
  let F := fullSubcomplexLift (fun f ↦ arrowVertexEdge f ∈ generatedEdges edges) (j ≫ v)
    (fun t ↦ fullSubcomplexOnVertices_vertex t)
  have hF : F ≫ generatedArrowInclusion edges = j ≫ v := fullSubcomplexLift_ι _ _ _
  have hsrc : F ≫ (generatedArrowInclusion edges ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)) = SSet.const x := by
    rw [← Category.assoc, hF, Category.assoc, vertexFiberι_comp, SSet.comp_const]
  let V := vertexFiberLift _ x F hsrc
  have hV : V ≫ w = F := vertexFiberLift_ι _ _ _ _
  have hVj : V ≫ generatedSourceArrowFiberInclusion edges x = j := by
    apply vertexFiber_hom_ext _ x
    rw [Category.assoc, generatedSourceArrowFiberInclusion_ι, ← Category.assoc, hV, hF]
  refine ⟨H, V, ?_, ?_⟩
  · apply (cancel_mono (generatedSourceArrowFiberInclusion edges x)).mp
    rw [Category.assoc, hVj, hH, Category.id_comp]
  · apply (cancel_mono j).mp
    rw [Category.assoc, hH, hVj, Category.id_comp]

/-- 全部分圏との同型は、元の厳密な fiber の包含を保持する。 -/
lemma generatedSourceArrowFullFiberIso_inclusion (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    (generatedSourceArrowFullFiberIso edges x).hom ≫
      (fullSubcomplexOnVertices _ (sourceArrowFiberCondition edges x)).ι =
      generatedSourceArrowFiberInclusion edges x :=
  fullSubcomplexLift_ι _ _
    (fun t : (generatedSourceArrowFiber edges x) _⦋0⦌ ↦ fullSubcomplexOnVertices_vertex t.val)

instance generatedSourceArrowFiber_quasicategory (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    Quasicategory (generatedSourceArrowFiber edges x) :=
  quasicategory_of_innerFibration (generatedSourceArrowFullFiberIso edges x).hom

/-- 周囲の fiber の元の閉包条件は、その fiber 内の同型で不変。 -/
lemma sourceArrowFiberCondition_iff_vertexIso (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    {f g : (vertexFiber (evaluateFunctorAt (Y := C)
      (stdSimplex.obj₀Equiv.symm 0 : Δ[1] _⦋0⦌)) x) _⦋0⦌} (e : VertexIso f g) :
    sourceArrowFiberCondition edges x f ↔ sourceArrowFiberCondition edges x g :=
  generatedArrow_mem_iff_vertexIso edges (VertexIso.map e (vertexFiberι _ x))

/-- 元の閉包内射 coslice から同じ始点の厳密な fiber への比較は同値。 -/
lemma generatedSourceToArrowFiber_isQCatEquivalence (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    IsQCatEquivalence (generatedSourceToArrowFiber edges x) := by
  let e := generatedSourceArrowFullFiberIso edges x
  let P := fun c : (sliceUnder (SSet.yonedaEquiv.symm x)) _⦋0⦌ ↦
    (JoinCocone.leg c (𝟙 Δ[0])).edge ∈ generatedEdges edges
  let R : (fullSubcomplexOnVertices (sliceUnder (SSet.yonedaEquiv.symm x)) P : SSet.{u + 1}) ⟶
      fullSubcomplexOnVertices _ (sourceArrowFiberCondition edges x) :=
    generatedSourceToArrowFiber edges x ≫ e.hom
  have hr : R ≫ (fullSubcomplexOnVertices _ (sourceArrowFiberCondition edges x)).ι =
      generatedSourceInclusion edges x ≫ (sourceCosliceArrowFiberEquivalence x).hom := by
    rw [Category.assoc, generatedSourceArrowFullFiberIso_inclusion, ← generatedSourceFiber_square]
  have hR : IsQCatEquivalence R := isQCatEquivalence_fullSubcomplexRestriction
    P (sourceArrowFiberCondition edges x)
    (fun h ↦ sourceArrowFiberCondition_iff_vertexIso edges x h)
    (sourceCosliceArrowFiberEquivalence x).hom
    (sourceCosliceArrowFiberEquivalence x).isQCatEquivalence R hr (by
      intro c hc
      have he := ConcreteCategory.congr_hom
        (NatTrans.congr_app (sourceCosliceArrowFiberEquivalence_inclusion x) (Opposite.op ⦋0⦌)) c
      change ((sourceCosliceArrowFiberEquivalence x).hom.app _ c).val =
        (sourceCosliceArrowFamily x).app _ c at he
      change arrowVertexEdge (((sourceCosliceArrowFiberEquivalence x).hom.app _ c).val) ∈ _ at hc
      rw [he, sourceCosliceArrowFamily_vertex] at hc
      exact hc)
  exact (qCatEquivalenceOfIso e).isQCatEquivalence.cancel_right hR

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
