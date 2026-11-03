module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTriangleLastSimplexObjects
/-!
概要：最大化側の最後辺と、第一射の全係数作用に続く最後射の実 head を一致させる。
方針：同じ二時刻の正規化式と、同じ反転係数の後合成の自然性を合成する。
規約：元の全係数と同じ実両端を保持する。
使われ方：Ncomp の実単体の全 Hom の一致。
-/

@[expose] public section
open CategoryTheory SSet SimplicialThickening MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
noncomputable section
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (s : SpaceInfinity.{u} _⦋2⦌)
/-- 概要：同じ元の二つの実単体は head 全体で一致する。
方針：各時刻の正規化式を合成し、同じ対象表示への移送を相殺する。
規約：全次数の係数と path を保持。使われ方：実単体の一致。 -/
lemma coherentTriangleLastSimplex_head {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌)
    (p : (SimplicialCategory.sHom pointKanObject (s.obj ⟨ULift.up 0⟩)).op _⦋n⦌)
    (j : Fin (n + 1)) :
    (coherentTriangleLastSourceSimplex s α p).map ⟨ULift.up 0⟩ ⟨ULift.up j.succ⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentTriangleLastSimplex_obj s α p 0)
        (coherentTriangleLastSimplex_obj s α p j.succ)) =
    (coherentTriangleLastCompositeSimplex s α p).map ⟨ULift.up 0⟩ ⟨ULift.up j.succ⟩ := by
  let f := coherentEdgeHom (SpaceInfinity.δ 2 s)
  let g := coherentEdgeHom (SpaceInfinity.δ 0 s)
  let p' := (SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject f)).app
    (Opposite.op ⦋n⦌) p
  have ht : α.toOrderHom j = 0 ∨ α.toOrderHom j = 1 :=
    (by decide : ∀ z : Fin 2, z = 0 ∨ z = 1) _
  rcases ht with hj | hj
  · apply simplicialHom_eq_of_display
      (hA := coherentTriangleLastSimplex_obj s α p 0)
      (hB := coherentTriangleLastSimplex_obj s α p j.succ) (kA := rfl)
      (kB := morphismInitialTail_obj_zero g α j hj)
    calc
      _ = pathFirstParameterMap j ≫ reflectedSimplexMap (SSet.yonedaEquiv.symm p) ≫
          eHomWhiskerLeft SSet pointKanObject f := by
        convert coherentTriangleLastInitialHead_zero s α p j hj using 1 <;> rfl
      _ = _ := by
        have h := morphismInitialHead_zero g pointKanObject α p' j hj
        change coneInitialHead pointKanObject (morphismInitialTail g α).val
          (SSet.yonedaEquiv.symm p') j ≫ _ = _ at h
        have hr := reflectedSimplexMap_post_app
          (eHomWhiskerLeft SSet pointKanObject f) p
        have hh := congrArg (fun k => pathFirstParameterMap j ≫ k) hr
        convert (h.trans hh).symm using 1 <;> rfl
  · apply simplicialHom_eq_of_display
      (hA := coherentTriangleLastSimplex_obj s α p 0)
      (hB := coherentTriangleLastSimplex_obj s α p j.succ) (kA := rfl)
      (kB := morphismInitialTail_obj_one g α j hj)
    calc
      _ = lift (pathFirstParameterMap j ≫ reflectedSimplexMap (SSet.yonedaEquiv.symm p) ≫
          eHomWhiskerLeft SSet pointKanObject f)
          (SSet.const (SimplicialCategory.homEquiv' _ _ g)) ≫
          eComp SSet pointKanObject (s.obj ⟨ULift.up 1⟩) (s.obj ⟨ULift.up 2⟩) := by
        convert coherentTriangleLastInitialHead_one s α p j hj using 1 <;> rfl
      _ = _ := by
        have h := morphismInitialHead_one g pointKanObject α p' j hj
        have hr := reflectedSimplexMap_post_app
          (eHomWhiskerLeft SSet pointKanObject f) p
        have hh := congrArg (fun k => lift (pathFirstParameterMap j ≫ k)
          (SSet.const (SimplicialCategory.homEquiv' _ _ g)) ≫
            eComp SSet pointKanObject (s.obj ⟨ULift.up 1⟩) (s.obj ⟨ULift.up 2⟩)) hr
        convert (h.trans hh).symm using 1 <;> rfl
end SerrePositivity.InfinityCategories.F2
