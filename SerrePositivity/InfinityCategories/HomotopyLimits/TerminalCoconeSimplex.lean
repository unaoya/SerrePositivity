module

public import SerrePositivity.InfinityCategories.HomotopyLimits.TerminalSimplex

/-!
# 通常右余錐の有限単体表示

概要：元の余錐を有限単体へ制限し、最後の頂点に元の余錐頂点を置く。
方針：同じ宇宙の ULift 順序添字に制限して終点拡張を適用する。
規約：元の通常余錐の join 写像と厳密に一致する。
使われ方：native roof prism の零端。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.TerminalCoconeSimplex
open CategoryTheory Limits SSet MonoidalCategory
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}
  (c : Cocone F) {n : ℕ} (Γ : Fin (n + 1) ⥤ I)

def lifted : ULift.{u} (Fin (n + 1)) ⥤ I :=
  (⟨ULift.down, fun _ _ h => h⟩ : ULift.{u} (Fin (n + 1)) →o Fin (n + 1)).toFunctor ⋙ Γ

def diagram : Fin (n + 2) ⥤ C :=
  TerminalSimplex.index n ⋙ SerrePositivity.InfinityCategories.F1B.coconeWithTerminalFunctor (c.whisker (lifted Γ))

lemma diagram_obj_cast (i : Fin (n + 1)) :
    (diagram c Γ).obj i.castSucc = F.obj (Γ.obj i) := by
  change (SerrePositivity.InfinityCategories.F1B.coconeWithTerminalFunctor (c.whisker (lifted Γ))).obj
    (TerminalSimplex.obj n i.castSucc) = _
  rw [TerminalSimplex.obj_cast]
  rfl

lemma diagram_obj_last : (diagram c Γ).obj (Fin.last (n + 1)) = c.pt := by
  change (SerrePositivity.InfinityCategories.F1B.coconeWithTerminalFunctor (c.whisker (lifted Γ))).obj
    (TerminalSimplex.obj n (Fin.last (n + 1))) = _
  rw [TerminalSimplex.obj_last]
  rfl

lemma diagram_map_cast_cast (i j : Fin (n + 1)) (hij : i ≤ j) :
    HEq ((diagram c Γ).map (homOfLE (Fin.castSucc_le_castSucc_iff.mpr hij)))
      (F.map (Γ.map (homOfLE hij))) := by
  exact TerminalSimplex.map_heq
    (SerrePositivity.InfinityCategories.F1B.coconeWithTerminalFunctor (c.whisker (lifted Γ)))
    (TerminalSimplex.obj_cast n i) (TerminalSimplex.obj_cast n j)
    ((TerminalSimplex.index n).map (homOfLE (Fin.castSucc_le_castSucc_iff.mpr hij)))
    (WithTerminal.incl.map (homOfLE
      (show (ULift.up i : ULift.{u} (Fin (n + 1))) ≤ ULift.up j from hij)))

lemma diagram_map_cast_last (i : Fin (n + 1)) :
    HEq ((diagram c Γ).map (homOfLE (Fin.le_last i.castSucc))) (c.ι.app (Γ.obj i)) := by
  exact TerminalSimplex.map_heq
    (SerrePositivity.InfinityCategories.F1B.coconeWithTerminalFunctor (c.whisker (lifted Γ)))
    (TerminalSimplex.obj_cast n i) (TerminalSimplex.obj_last n)
    ((TerminalSimplex.index n).map (homOfLE (Fin.le_last i.castSucc)))
    (WithTerminal.homFrom (ULift.up i))

lemma lifted_nerve : (stdSimplex.isoNerve n).hom ≫ nerveMap (lifted Γ) =
    SSet.yonedaEquiv.symm (show (nerve I) _⦋n⦌ from Γ) := by
  rfl

lemma diagram_join :
    (joinStdSimplexIso n 0).hom ≫
      SSet.yonedaEquiv.symm (show (nerve C) _⦋n + 1⦌ from diagram c Γ) =
    joinMap (SSet.yonedaEquiv.symm (show (nerve I) _⦋n⦌ from Γ))
      (𝟙 (Δ[0] : SSet.{u})) ≫ (SerrePositivity.InfinityCategories.F1B.nerveCoconeEquiv c).val := by
  have h : SSet.yonedaEquiv.symm
      (show (nerve C) _⦋n + 1⦌ from diagram c Γ) =
      SSet.yonedaEquiv.symm
        (show (nerve _) _⦋n + 1⦌ from TerminalSimplex.index n) ≫
        nerveMap (SerrePositivity.InfinityCategories.F1B.coconeWithTerminalFunctor (c.whisker (lifted Γ))) := by
    rfl
  rw [h, ← Category.assoc, TerminalSimplex.index_join, Category.assoc,
    SerrePositivity.InfinityCategories.F1B.nerveCocone_withTerminal, ← SerrePositivity.InfinityCategories.F1B.nerveCocone_whisker]
  rw [← Category.assoc, ← joinMap_comp, lifted_nerve, Category.id_comp]

end SerrePositivity.EInfinity.FrameHom.TerminalCoconeSimplex
