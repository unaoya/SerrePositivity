module
public import SerrePositivity.KST.SConstruction.PointedKanDiagramTriangleComponents
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-! # 図式全体の比較逆射の三角形と元の成分の逆条件
概要：関手同型の逆の代表を、元の比較と両方向の恒等辺を保つ三角形で照合する。
方針：関手同型の逆律を指定三辺の実三角形へ戻し、対象ごとの点つき成分へ反映する。
規約：全体の逆の代表を対象ごとに選び直さない。
使われ方：一方向比較の元の Whitehead 逆との成分一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 関手の辺を円柱へ戻して再び curry すると元の辺。 -/
lemma diagramFunctorEdge_homotopy_roundtrip {A X : SSet.{u}} {f g : A ⟶ X}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((CategoryTheory.ihom A).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e) = e := by
  ext
  change SSet.yonedaEquiv (CategoryTheory.MonoidalClosed.curry
    (CategoryTheory.MonoidalClosed.uncurry (SSet.yonedaEquiv.symm e.edge))) = e.edge
  rw [CategoryTheory.MonoidalClosed.curry_uncurry, Equiv.apply_symm_apply]

/-- 図式全体の同型の順方向の射は元の比較の円柱の辺の類。 -/
lemma pointedKanDiagramFunctorIso_hom {I : Type u} [SmallCategory I]
    {F G : I ⥤ PointedSimplicialSet.{u}}
    (hF : ∀ i, KanComplex (F.obj i).right) (hG : ∀ i, KanComplex (G.obj i).right)
    (η : F ⟶ G) (hη : ∀ i, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (η.app i).right) :
    (pointedKanDiagramFunctorIso hF hG η hη).hom =
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (pointedKanDiagramHomotopy hF hG η)) := rfl

/-- 選んだ全体逆の円柱の辺の類は元の図式同型の逆射。 -/
lemma pointedKanDiagramInverseHomotopy_hom {I : Type u} [SmallCategory I]
    {F G : I ⥤ PointedSimplicialSet.{u}}
    (hF : ∀ i, KanComplex (F.obj i).right) (hG : ∀ i, KanComplex (G.obj i).right)
    (η : F ⟶ G) (hη : ∀ i, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (η.app i).right) :
    SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (pointedKanDiagramInverseHomotopy hF hG η hη)) =
      (pointedKanDiagramFunctorIso hF hG η hη).inv := by
  dsimp only [pointedKanDiagramInverseHomotopy]
  rw [diagramFunctorEdge_homotopy_roundtrip, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge_homMk]
  rfl

/-- 元の比較と全体逆は、源の恒等円柱を第三辺に持つ実三角形をなす。 -/
lemma pointedKanDiagramInverse_leftTriangle_nonempty {I : Type u} [SmallCategory I]
    {F G : I ⥤ PointedSimplicialSet.{u}}
    (hF : ∀ i, KanComplex (F.obj i).right) (hG : ∀ i, KanComplex (G.obj i).right)
    (η : F ⟶ G) (hη : ∀ i, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (η.app i).right) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle (pointedKanDiagramHomotopy hF hG η)
      (pointedKanDiagramInverseHomotopy hF hG η hη)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (pointedKanCoherentDiagram F hF))) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.nonempty_functorCompositionTriangle_of_homEq
  rw [pointedKanDiagramInverseHomotopy_hom, ← pointedKanDiagramFunctorIso_hom hF hG η hη,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl_hom]
  exact (pointedKanDiagramFunctorIso hF hG η hη).hom_inv_id

/-- 全体逆と元の比較は、標的の恒等円柱を第三辺に持つ実三角形をなす。 -/
lemma pointedKanDiagramInverse_rightTriangle_nonempty {I : Type u} [SmallCategory I]
    {F G : I ⥤ PointedSimplicialSet.{u}}
    (hF : ∀ i, KanComplex (F.obj i).right) (hG : ∀ i, KanComplex (G.obj i).right)
    (η : F ⟶ G) (hη : ∀ i, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (η.app i).right) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle (pointedKanDiagramInverseHomotopy hF hG η hη)
      (pointedKanDiagramHomotopy hF hG η)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (pointedKanCoherentDiagram G hG))) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.nonempty_functorCompositionTriangle_of_homEq
  rw [pointedKanDiagramInverseHomotopy_hom, ← pointedKanDiagramFunctorIso_hom hF hG η hη,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl_hom]
  exact (pointedKanDiagramFunctorIso hF hG η hη).inv_hom_id

/-- 恒等円柱から元の模型へ戻した点つき射は恒等射そのもの。 -/
lemma pointedKanDiagramHomotopyMapAt_refl {I : Type u} [SmallCategory I]
    (F : I ⥤ PointedSimplicialSet.{u}) (hF : ∀ i, KanComplex (F.obj i).right) (i : I) :
    pointedKanDiagramHomotopyMapAt hF hF
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (pointedKanCoherentDiagram F hF)) i = 𝟙 (F.obj i) := by
  let e := pointedKanDiagramHomotopyEdgeAt hF hF
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (pointedKanCoherentDiagram F hF)) i
  have he : e = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (𝟙 ((pointedKanDiagram F hF).obj i)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_id]
    apply SSet.Edge.ext
    change (pointedKanCoherentDiagram F hF).app (Opposite.op ⦋1⦌)
      (((SSet.uliftFunctor.{u+1,u}).obj (nerve I)).σ 0 (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))) =
        PointedKanInfinity.σ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((pointedKanDiagram F hF).obj i))
    rw [σ_naturality_apply]
    exact congrArg (PointedKanInfinity.σ 0)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_vertex (pointedKanDiagram F hF) i)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom e).hom = _
  rw [he, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom_edge]
  rfl

/-- 対象で回収した全体逆は、元の比較の左逆の点つき成分を持つ。 -/
lemma pointedKanDiagramInverse_left_component {I : Type u} [SmallCategory I]
    {F G : I ⥤ PointedSimplicialSet.{u}}
    (hF : ∀ i, KanComplex (F.obj i).right) (hG : ∀ i, KanComplex (G.obj i).right)
    (η : F ⟶ G) (hη : ∀ i, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (η.app i).right) (i : I) :
    componentOf (η.app i ≫ pointedKanDiagramHomotopyMapAt hG hF
      (pointedKanDiagramInverseHomotopy hF hG η hη) i) = componentOf (𝟙 (F.obj i)) := by
  obtain ⟨T⟩ := pointedKanDiagramInverse_leftTriangle_nonempty hF hG η hη
  have hc := pointedKanDiagramTriangle_components hF hG hF _ _ _ T i
  rw [pointedKanDiagramHomotopyMapAt_natTrans, pointedKanDiagramHomotopyMapAt_refl] at hc
  exact hc

/-- 対象で回収した全体逆は、元の比較の右逆の点つき成分を持つ。 -/
lemma pointedKanDiagramInverse_right_component {I : Type u} [SmallCategory I]
    {F G : I ⥤ PointedSimplicialSet.{u}}
    (hF : ∀ i, KanComplex (F.obj i).right) (hG : ∀ i, KanComplex (G.obj i).right)
    (η : F ⟶ G) (hη : ∀ i, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (η.app i).right) (i : I) :
    componentOf (pointedKanDiagramHomotopyMapAt hG hF
      (pointedKanDiagramInverseHomotopy hF hG η hη) i ≫ η.app i) = componentOf (𝟙 (G.obj i)) := by
  obtain ⟨T⟩ := pointedKanDiagramInverse_rightTriangle_nonempty hF hG η hη
  have hc := pointedKanDiagramTriangle_components hG hF hG _ _ _ T i
  rw [pointedKanDiagramHomotopyMapAt_natTrans, pointedKanDiagramHomotopyMapAt_refl] at hc
  exact hc

end SerrePositivity.KST.SConstruction
