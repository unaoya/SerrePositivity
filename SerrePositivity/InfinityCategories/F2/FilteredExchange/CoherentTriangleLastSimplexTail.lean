module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTriangleLastSimplexObjects
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTriangleLastTailValues

/-!
概要：同じ二つの実単体の正頂点間の全 Hom を一致させる。
方針：三つの可能な時刻配置で同じ指定射へ揃え、逆順は元の path から除く。
規約：元の全次数の係数と path を保持する。
使われ方：Ncomp の実単体の全 Hom の一致。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet SimplicialThickening MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (s : SpaceInfinity.{u} _⦋2⦌)

/-- 概要：順方向の正頂点間 Hom は同じ元の実単体で一致する。
方針：同じ時刻配置の指定射を比較する。
規約：全 Hom を保持。使われ方：実 tail 全体の一致。 -/
lemma coherentTriangleLastSimplex_tail_of_le {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌)
    (p : (SimplicialCategory.sHom pointKanObject (s.obj ⟨ULift.up 0⟩)).op _⦋n⦌)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    (coherentTriangleLastSourceSimplex s α p).map ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentTriangleLastSimplex_obj s α p i.succ)
        (coherentTriangleLastSimplex_obj s α p j.succ)) =
    (coherentTriangleLastCompositeSimplex s α p).map ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ := by
  let g := coherentEdgeHom (SpaceInfinity.δ 0 s)
  have hi : α.toOrderHom i = 0 ∨ α.toOrderHom i = 1 :=
    (by decide : ∀ z : Fin 2, z = 0 ∨ z = 1) _
  have hj : α.toOrderHom j = 0 ∨ α.toOrderHom j = 1 :=
    (by decide : ∀ z : Fin 2, z = 0 ∨ z = 1) _
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · apply simplicialHom_eq_of_display
      (hA := coherentTriangleLastSimplex_obj s α p i.succ)
      (hB := coherentTriangleLastSimplex_obj s α p j.succ)
      (kA := morphismInitialTail_obj_zero g α i hi)
      (kB := morphismInitialTail_obj_zero g α j hj)
    calc
      _ = SSet.const (SimplicialCategory.homEquiv' _ _ (𝟙 (s.obj ⟨ULift.up 1⟩))) := by
        convert coherentTriangleLastTail_tail_zero s α i j hij hi hj using 1 <;> rfl
      _ = _ := by
        have h := morphismInitialTail_map_labels g α (ULift.up i.succ) (ULift.up j.succ)
          (Fin.succ_le_succ_iff.mpr hij) 0 0 hi hj (by decide)
        convert h.symm using 1 <;> rfl
  · apply simplicialHom_eq_of_display
      (hA := coherentTriangleLastSimplex_obj s α p i.succ)
      (hB := coherentTriangleLastSimplex_obj s α p j.succ)
      (kA := morphismInitialTail_obj_zero g α i hi)
      (kB := morphismInitialTail_obj_one g α j hj)
    calc
      _ = SSet.const (SimplicialCategory.homEquiv' _ _ g) := by
        convert coherentTriangleLastTail_tail_mixed s α i j hij hi hj using 1 <;> rfl
      _ = _ := by
        have h := morphismInitialTail_map_labels g α (ULift.up i.succ) (ULift.up j.succ)
          (Fin.succ_le_succ_iff.mpr hij) 0 1 hi hj (by decide)
        convert h.symm using 1 <;> rfl
  · have h := α.toOrderHom.monotone hij
    rw [hi, hj] at h
    exact False.elim ((by decide : ¬(1 : Fin 2) ≤ 0) h)
  · apply simplicialHom_eq_of_display
      (hA := coherentTriangleLastSimplex_obj s α p i.succ)
      (hB := coherentTriangleLastSimplex_obj s α p j.succ)
      (kA := morphismInitialTail_obj_one g α i hi)
      (kB := morphismInitialTail_obj_one g α j hj)
    calc
      _ = SSet.const (SimplicialCategory.homEquiv' _ _ (𝟙 (s.obj ⟨ULift.up 2⟩))) := by
        convert coherentTriangleLastTail_tail_one s α i j hij hi hj using 1 <;> rfl
      _ = _ := by
        have h := morphismInitialTail_map_labels g α (ULift.up i.succ) (ULift.up j.succ)
          (Fin.succ_le_succ_iff.mpr hij) 1 1 hi hj (by decide)
        convert h.symm using 1 <;> rfl

/-- 概要：正頂点間 Hom は順序を仮定せず一致する。方針：元の path が順序を与える。
規約：元の path を保持。使われ方：実単体の外延性。 -/
lemma coherentTriangleLastSimplex_tail {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌)
    (p : (SimplicialCategory.sHom pointKanObject (s.obj ⟨ULift.up 0⟩)).op _⦋n⦌)
    (i j : Fin (n + 1)) :
    (coherentTriangleLastSourceSimplex s α p).map ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentTriangleLastSimplex_obj s α p i.succ)
        (coherentTriangleLastSimplex_obj s α p j.succ)) =
    (coherentTriangleLastCompositeSimplex s α p).map ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ := by
  by_cases hij : i ≤ j
  · exact coherentTriangleLastSimplex_tail_of_le s α p i j hij
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have h := Path.le (P.obj 0)
    change i.succ ≤ j.succ at h
    exact False.elim (hij (Fin.succ_le_succ_iff.mp h))
end SerrePositivity.InfinityCategories.F2
