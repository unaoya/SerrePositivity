module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.KanDiagramLeftHomCutSimplex

/-!
概要：左区間の実際の対角評価は、底・時刻・変換を同時に制限する全ての面・退化と可換。
方針：元の区間 prism の単体的自然性を、その実際の全評価へ戻す。
規約：tail の退化拡張全体の自然性を仮定しない。
使われ方：weighted cone の head の自然性と、始点固定の cone の全単体の貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories


/-- 元の左区間の対角単体は、全ての面・退化への同時制限と厳密に可換。 -/
lemma kanDiagramLeftHomCutSimplex_naturality {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (σ : (nerve I) _⦋n⦌)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.map α.op (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex F G σ s t) =
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex F G ((nerve I).map α.op σ)
        ((SimplicialCategory.sHom F G).op.map α.op s) (Δ[1].map α.op t) := by
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramLeftHomInterval (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramUniversalEnriched I) F G rfl rfl))
  have hn := P.naturality α.op
  have h := congrArg (fun f => f ((t, ULift.up σ), ULift.up s)) hn
  change P.app (Opposite.op ⦋m⦌)
      ((Δ[1].map α.op t, ULift.up ((nerve I).map α.op σ)),
        ULift.up ((SimplicialCategory.sHom F G).op.map α.op s)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.map α.op (P.app (Opposite.op ⦋n⦌) ((t, ULift.up σ), ULift.up s)) at h
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.map α.op (P.app (Opposite.op ⦋n⦌) ((t, ULift.up σ), ULift.up s)) :=
      congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.map α.op) (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_prism F G σ s t).symm
    _ = _ := h.symm
    _ = _ := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_prism F G ((nerve I).map α.op σ)
      ((SimplicialCategory.sHom F G).op.map α.op s) (Δ[1].map α.op t)

/-- 同じ自然性は、元の正頂点の対象の表示を面・退化後の表示へ移す厳密な等式を与える。 -/
lemma kanDiagramLeftHomCutSimplex_obj_reindex {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (σ : (nerve I) _⦋n⦌)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) (j : Fin (m + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex F G σ s t).obj ⟨ULift.up (α.toOrderHom j)⟩ =
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex F G ((nerve I).map α.op σ)
        ((SimplicialCategory.sHom F G).op.map α.op s) (Δ[1].map α.op t)).obj ⟨ULift.up j⟩ := by
  exact congrArg (fun A : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋m⦌ => A.obj ⟨ULift.up j⟩)
    (kanDiagramLeftHomCutSimplex_naturality F G α σ s t)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
