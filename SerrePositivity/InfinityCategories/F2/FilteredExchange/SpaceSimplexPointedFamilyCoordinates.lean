module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedCoherentMorphismPrism
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedCoherentCosliceNormalization

/-!
概要：元の実 pointed 族の全次数の単体を、同じ初点固定の拡張単体で読む。
方針：coslice の実座標の制限と同じ全 Hom の前合成を計算する。
規約：初点を保たない係数制限でも元の初点を保持。使われ方：実 prism の全係数照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 元の全 pointed 族を任意の標準単体で評価した実座標の厳密な式。 -/
lemma spaceSimplexPointedFamily_coordinates {m n : ℕ} (s : SpaceInfinity.{u} _⦋n⦌)
    (α : ⦋m⦌ ⟶ ⦋n⦌)
    (p : (SimplicialCategory.sHom pointKanObject (s.obj ⟨ULift.up 0⟩)).op _⦋m⦌) :
    SSet.yonedaEquiv ((leftPointStdSimplexIso m).inv ≫
      ((spaceSimplexPointedFamily s).app (Opposite.op ⦋m⦌)
        (stdSimplex.objEquiv.symm α, ULift.up p)).val) =
    coneInitialFixedSimplex pointKanObject
      (fixedInitialSimplexReindex (s.obj ⟨ULift.up 0⟩) α
        (⟨coherentConeTailExtension s, rfl⟩ :
          fixedInitialSimplex (s.obj ⟨ULift.up 0⟩) n)) (SSet.yonedaEquiv.symm p) := by
  change SSet.yonedaEquiv ((leftPointStdSimplexIso m).inv ≫
    (pointedCoherentCosliceIso.hom.app (Opposite.op ⦋m⦌)
      (cosliceSourcePrecompositionSimplex pointKanObject (s.obj ⟨ULift.up 0⟩)
        ((SSet.yonedaEquiv.symm (spaceSimplexSourceCone s)).app (Opposite.op ⦋m⦌)
          (stdSimplex.objEquiv.symm α)) p)).val) = _
  rw [pointedCoherentCosliceIso_app_val]
  change SSet.yonedaEquiv ((leftPointStdSimplexIso m).inv ≫
    ((leftPointStdSimplexIso m).hom ≫ SSet.yonedaEquiv.symm
      (coneInitialFixedSimplex pointKanObject
        (cosliceInitialCoordinates (s.obj ⟨ULift.up 0⟩)
          ((SSet.yonedaEquiv.symm (spaceSimplexSourceCone s)).app (Opposite.op ⦋m⦌)
            (stdSimplex.objEquiv.symm α))) (SSet.yonedaEquiv.symm p)))) = _
  rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply,
    SSet.yonedaEquiv_symm_app_objEquiv_symm, cosliceInitialCoordinates_reindex,
    spaceSimplexSourceCone_initialCoordinates]

/-- 元の固定射の実 prism の全単体も、元の同じ初点固定の拡張で読む。 -/
lemma pointedCoherentMorphismPrism_coordinates {K L : KanObject.{u}} (f : K ⟶ L)
    {n : ℕ} (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌)
    (p : (SimplicialCategory.sHom pointKanObject K).op _⦋n⦌) :
    SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫
      ((pointedCoherentMorphismPrism f).app (Opposite.op ⦋n⦌) (t, ULift.up p)).val) =
    coneInitialFixedSimplex pointKanObject
      (fixedInitialSimplexReindex K (stdSimplex.objEquiv t)
        (⟨coherentConeTailExtension (coherentNerveEdge f).edge, rfl⟩ :
          fixedInitialSimplex K 1)) (SSet.yonedaEquiv.symm p) := by
  have h := spaceSimplexPointedFamily_coordinates (coherentNerveEdge f).edge
    (stdSimplex.objEquiv t) p
  rw [Equiv.symm_apply_apply] at h
  exact h

end SerrePositivity.InfinityCategories.F2
