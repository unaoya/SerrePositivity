module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedEdges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRepresentableDerivedMaps
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.UniverseCofiberEdges

/-! # 閉 dg 射の native 実分母と主導来分母の一致

概要：閉射の native 実辺が Verdier 分母であることは、その Yoneda 導来像の trW と同値。
方針：同じ一次単体を保った実 Yoneda と宇宙持ち上げで分母を比較し、標準 cone で判定する。
規約：元の Hom の平坦性を要求しない。使われ方：閉 dg roof の実分母への昇格。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 閉 dg 射の native 実辺の分母条件は、同じ射の主導来 Yoneda 像の trW と同値。 -/
theorem dgClosedEdge_mem_iff_derived_trW (P : Set D) {x y : _root_.SerrePositivity.DifferentialGraded.ClosedCategory A D}
    (f : x ⟶ y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D f).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ↔
      (derivedFiniteCellOver A D P).trW (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D f) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isStable_of_pretriangulated A D
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveULift_isStable_of_pretriangulated A D
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftNerve_isStable A D
  let i := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso.{u, v, max (u + 1) v} A D
  let U := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, v, max (u + 1) v} A D
  let J := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) v} A D).comp (dgYoneda A D)
  let F := i.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map J
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor i.hom :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso i).isQCatEquivalence
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map J) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulatedYoneda_isExactFunctor A D
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful F :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso i).isQCatEquivalence.isFullyFaithful.comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulatedYoneda_isFullyFaithful A D)
  have hP : F.app (Opposite.op ⦋0⦌) '' (ULift.up '' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' P)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleGeneratorVertices A D P := by
    change (fun a => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map J).app (Opposite.op ⦋0⦌)
      (i.hom.app (Opposite.op ⦋0⦌) a)) '' _ = _
    rw [← Set.image_image, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLiftedGeneratorVertices_universe_image,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLiftedGeneratorVertices_yoneda_image]
  have hJ : U.comp J = dgYoneda A D := by
    apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex A) (fun _ => rfl)
    intro a b
    simp only [EnrichedFunctor.comp_map, U, J, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown,
      _root_.SerrePositivity.InfinityCategories.dgObjectImageEvaluation, Category.id_comp, eqToHom_refl, Category.comp_id]
  have he : ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftEdge.{max u v, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D f)).map
      ((truncation 2).map F)).edge =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D ((dgYoneda A D).onClosed.map f)).edge := by
    change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D f).edge.map U).map J = _
    have h : ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D f).edge.map U).map J =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D f).edge.map (dgYoneda A D) := by
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
      change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D f).edge.toSimplexData.map U).map J = _
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_comp, hJ]
      rfl
    exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_map A D (dgYoneda A D) f)
  have hmap := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_map_iff F hf
    (ULift.up '' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' P))
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftEdge.{max u v, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D f))
  rw [hP, he] at hmap
  have hnative := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_ulift_iff.{max u v, max (u + 1) v}
    (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' P) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D f)
  have hcone := (_root_.SerrePositivity.DifferentialGraded.homotopyFiniteCellOver A D Set.univ).ext_of_isTriangulatedClosed₃
    (_root_.SerrePositivity.DifferentialGraded.moduleHomotopyConeTriangle A D ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map f))
    (_root_.SerrePositivity.DifferentialGraded.moduleHomotopyConeTriangle_distinguished A D _)
    ((_root_.SerrePositivity.DifferentialGraded.moduleFiniteCellOver A D Set.univ).prop_map_obj (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy A D)
      (_root_.SerrePositivity.DifferentialGraded.moduleFiniteCell_representable A D x))
    ((_root_.SerrePositivity.DifferentialGraded.moduleFiniteCellOver A D Set.univ).prop_map_obj (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy A D)
      (_root_.SerrePositivity.DifferentialGraded.moduleFiniteCell_representable A D y))
  have hcell := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyFiniteCell_iff_derivedFiniteCell A D P _ hcone).trans
    ((_root_.SerrePositivity.DifferentialGraded.derivedFiniteCellOver A D P).prop_iff_of_iso ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso A D).app _))
  have htr := (_root_.SerrePositivity.DifferentialGraded.derivedFiniteCellOver A D P).trW_iff_of_distinguished
    (_root_.SerrePositivity.DifferentialGraded.moduleDerivedConeTriangle A D ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map f))
    (_root_.SerrePositivity.DifferentialGraded.moduleDerivedConeTriangle_distinguished A D _)
  exact hnative.symm.trans (hmap.symm.trans
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModule_cofiberEdges_iff_finiteCell A D P _).trans (hcell.trans htr.symm)))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
