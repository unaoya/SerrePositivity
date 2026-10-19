module
public import SerrePositivity.InfinityCategories.Derived.DGClosedEdges
public import SerrePositivity.InfinityCategories.Derived.DGRepresentableDerivedMaps
public import SerrePositivity.InfinityCategories.Stable.UniverseCofiberEdges

/-! # 閉 dg 射の native 実分母と主導来分母の一致

概要：閉射の native 実辺が Verdier 分母であることは、その Yoneda 導来像の trW と同値。
方針：同じ一次単体を保った実 Yoneda と宇宙持ち上げで分母を比較し、標準 cone で判定する。
規約：元の Hom の平坦性を要求しない。使われ方：閉 dg roof の実分母への昇格。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 閉 dg 射の native 実辺の分母条件は、同じ射の主導来 Yoneda 像の trW と同値。 -/
theorem dgClosedEdge_mem_iff_derived_trW (P : Set D) {x y : ClosedCategory A D}
    (f : x ⟶ y) :
    (dgClosedEdge A D f).edge ∈ dgVerdierEdges A D P ↔
      (derivedFiniteCellOver A D P).trW (dgRepresentableDerivedMap A D f) := by
  let := dgNerve_isStable_of_pretriangulated A D
  let := dgNerveULift_isStable_of_pretriangulated A D
  let := dgUniverseLiftNerve_isStable A D
  let i := dgNerveUniverseLiftIso.{u, v, max (u + 1) v} A D
  let U := dgUniverseLiftUp.{u, v, max (u + 1) v} A D
  let J := (dgUniverseLiftDown.{u, v, max (u + 1) v} A D).comp (dgYoneda A D)
  let F := i.hom ≫ dgNerve.map J
  let : IsExactFunctor i.hom :=
    isExactFunctor_of_isQCatEquivalence (qCatEquivalenceOfIso i).isQCatEquivalence
  let : IsExactFunctor (dgNerve.map J) := dgPretriangulatedYoneda_isExactFunctor A D
  have hf : IsFullyFaithful F :=
    (qCatEquivalenceOfIso i).isQCatEquivalence.isFullyFaithful.comp
      (dgPretriangulatedYoneda_isFullyFaithful A D)
  have hP : F.app (Opposite.op ⦋0⦌) '' (ULift.up '' (Simplex.vertex '' P)) =
      dgModuleGeneratorVertices A D P := by
    change (fun a => (dgNerve.map J).app (Opposite.op ⦋0⦌)
      (i.hom.app (Opposite.op ⦋0⦌) a)) '' _ = _
    rw [← Set.image_image, dgLiftedGeneratorVertices_universe_image,
      dgLiftedGeneratorVertices_yoneda_image]
  have hJ : U.comp J = dgYoneda A D := by
    apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
    intro a b
    simp only [EnrichedFunctor.comp_map, U, J, dgUniverseLiftUp, dgUniverseLiftDown,
      dgObjectImageEvaluation, Category.id_comp, eqToHom_refl, Category.comp_id]
  have he : ((uliftEdge.{max u v, max (u + 1) v} (dgClosedEdge A D f)).map
      ((truncation 2).map F)).edge =
        (dgModuleEdge A D ((dgYoneda A D).onClosed.map f)).edge := by
    change ((dgClosedEdge A D f).edge.map U).map J = _
    have h : ((dgClosedEdge A D f).edge.map U).map J =
        (dgClosedEdge A D f).edge.map (dgYoneda A D) := by
      apply Simplex.ext
      change ((dgClosedEdge A D f).edge.toSimplexData.map U).map J = _
      rw [← SimplexData.map_comp, hJ]
      rfl
    exact h.trans (dgClosedEdge_map A D (dgYoneda A D) f)
  have hmap := cofiberStableEdges_map_iff F hf
    (ULift.up '' (Simplex.vertex '' P))
    (uliftEdge.{max u v, max (u + 1) v} (dgClosedEdge A D f))
  rw [hP, he] at hmap
  have hnative := cofiberStableEdges_ulift_iff.{max u v, max (u + 1) v}
    (X := dgNerve A D) (Simplex.vertex '' P) (dgClosedEdge A D f)
  have hcone := (homotopyFiniteCellOver A D Set.univ).ext_of_isTriangulatedClosed₃
    (moduleHomotopyConeTriangle A D ((dgYoneda A D).onClosed.map f))
    (moduleHomotopyConeTriangle_distinguished A D _)
    ((moduleFiniteCellOver A D Set.univ).prop_map_obj (moduleToHomotopy A D)
      (moduleFiniteCell_representable A D x))
    ((moduleFiniteCellOver A D Set.univ).prop_map_obj (moduleToHomotopy A D)
      (moduleFiniteCell_representable A D y))
  have hcell := (dgHomotopyFiniteCell_iff_derivedFiniteCell A D P _ hcone).trans
    ((derivedFiniteCellOver A D P).prop_iff_of_iso ((moduleToHomotopyDerivedIso A D).app _))
  have htr := (derivedFiniteCellOver A D P).trW_iff_of_distinguished
    (moduleDerivedConeTriangle A D ((dgYoneda A D).onClosed.map f))
    (moduleDerivedConeTriangle_distinguished A D _)
  exact hnative.symm.trans (hmap.symm.trans
    ((dgModule_cofiberEdges_iff_finiteCell A D P _).trans (hcell.trans htr.symm)))

end SerrePositivity.InfinityCategories
