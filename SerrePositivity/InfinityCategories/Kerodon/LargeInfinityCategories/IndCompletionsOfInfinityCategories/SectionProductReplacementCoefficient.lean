module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.RelativeSectionMixedEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexFirstVertex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacement

/-!
概要：全単体の切断の replacement の始点係数を、元の strict 図式の同じ係数へ評価する。
方針：底の射列の初頂点座標と元の相対切断を対角に評価する。
規約：元の底の射列と係数を保持し、面・退化の始点移動を同じ式で扱う。
使われ方：全切断の replacement から共同 weighted 全空間への大域射。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Category.{u} I] {B : SSet.{u}} (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B)

/-- 底の全単体と元の添字を同時に動かす、同じ全切断の小さい Kan 図式。 -/
def strictLeftTransportSectionDiagram : I × _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftSectionProductDiagram F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B)

/-- 元の replacement の始点係数を、底の全射列の初頂点座標で評価する。 -/
def sectionProductReplacementCoefficient {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex
      (strictLeftTransportSectionDiagram F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) n) :
    (Δ[n] : SSet.{u}) ⟶ (F.obj (s.1.obj 0).1).val.left :=
  lift (SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMorphism
    (s.1 ⋙ CategoryTheory.Prod.snd I (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)))) (𝟙 _) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry s.2

/-- 同じ始点係数評価は、面・退化の始点移動と元の strict な輸送に関して自然。 -/
lemma sectionProductReplacementCoefficient_naturality {m n : SimplexCategory} (α : m ⟶ n)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex
      (strictLeftTransportSectionDiagram F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) n.len) :
    sectionProductReplacementCoefficient F
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplexMap _ α s) =
      SSet.stdSimplex.map α ≫ sectionProductReplacementCoefficient F s ≫
        (F.map (s.1.map (homOfLE (Fin.zero_le (α.toOrderHom 0)))).1).left := by
  let σ := s.1 ⋙ CategoryTheory.Prod.snd I (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)
  let g := s.1.map (homOfLE (Fin.zero_le (α.toOrderHom 0)))
  let r := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B).map g.2.op
  have hcoord : SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMorphism
      ((SimplexCategory.toCat.map α).toFunctor ⋙ σ)) ≫ r.left =
      SSet.stdSimplex.map α ≫ SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMorphism σ) := by
    have h := congrArg (fun q ↦ (SSet.stdSimplex.map q : (Δ[m.len] : SSet.{u}) ⟶
      SSet.stdSimplex.obj (σ.obj 0).objDown.obj.unop))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMorphism_naturality α σ)
    simp only [CategoryTheory.Functor.map_comp] at h
    exact h
  change lift (SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMorphism
      ((SimplexCategory.toCat.map α).toFunctor ⋙ σ))) (𝟙 _) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (((SSet.stdSimplex.map α ≫ s.2) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost _ _ (F.map g.1).left (Over.w (F.map g.1)) _) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre _ r) = _
  have hmain := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeSection_mixedDiagonal
    (F.obj (s.1.obj 0).1).val.hom (F.obj (s.1.obj (α.toOrderHom 0)).1).val.hom
    (F.map g.1).left (Over.w (F.map g.1)) r s.2 (SSet.stdSimplex.map α)
    (SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMorphism
      ((SimplexCategory.toCat.map α).toFunctor ⋙ σ))) (𝟙 (Δ[m.len] : SSet.{u}))
  rw [hmain, Category.id_comp, hcoord]
  rw [sectionProductReplacementCoefficient]
  simp only [← Category.assoc, comp_lift, Category.comp_id]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
