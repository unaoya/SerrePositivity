module

public import SerrePositivity.InfinityCategories.F2.SpaceSimplexPointedAugmentation

/-!
概要：一点を前置した全単体の Hom を、元の全 Hom と同じ係数で計算する。
方針：head 置換の四分岐を展開し、正頂点間の厳密な tail 公式を代入する。
規約：反転 Hom 係数を反転していない右 Hom 係数に取り替えない。
使われ方：三つの pointed 面の比較で、指定精密化と全係数を追跡する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {n : ℕ} (s : SpaceInfinity.{u} _⦋n⦌)
  (p : (Δ[n] : SSet.{u}) ⟶ (SimplicialCategory.sHom pointKanObject
    (s.obj ⟨ULift.up 0⟩)).op)

/-- 新しい初点からの全 Hom は、元の全係数で構成した head そのもの。 -/
lemma spaceSimplexPointedAugmentation_head (j : Fin (n + 1)) :
    (spaceSimplexPointedAugmentation s p).map ⟨ULift.up 0⟩ ⟨ULift.up j.succ⟩ =
      coneInitialHead pointKanObject (coherentConeTailExtension s) p j := rfl

/-- 正頂点間の全 Hom は、元の全 Hom の正頂点の path 移送だけを伴う。 -/
lemma spaceSimplexPointedAugmentation_tailMap (i j : Fin (n + 1)) :
    (spaceSimplexPointedAugmentation s p).map
        ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ =
      (pathPositiveShiftIso i j).inv ≫ s.map ⟨ULift.up i⟩ ⟨ULift.up j⟩ :=
  coherentConeTailExtension_map s i j

/-- head の合成は、元の正頂点間の全 Hom と厳密に整合する。 -/
lemma spaceSimplexPointedAugmentation_head_comp (i j : Fin (n + 1)) :
    eComp SSet
        (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫
      (spaceSimplexPointedAugmentation s p).map ⟨ULift.up 0⟩ ⟨ULift.up j.succ⟩ =
    ((spaceSimplexPointedAugmentation s p).map ⟨ULift.up 0⟩ ⟨ULift.up i.succ⟩ ⊗ₘ
      ((pathPositiveShiftIso i j).inv ≫ s.map ⟨ULift.up i⟩ ⟨ULift.up j⟩)) ≫
        eComp SSet pointKanObject (s.obj ⟨ULift.up i⟩) (s.obj ⟨ULift.up j⟩) := by
  have h := coneInitialHead_comp pointKanObject (coherentConeTailExtension s) p i j
  rw [coherentConeTailExtension_map] at h
  exact h

end SerrePositivity.InfinityCategories.F2
