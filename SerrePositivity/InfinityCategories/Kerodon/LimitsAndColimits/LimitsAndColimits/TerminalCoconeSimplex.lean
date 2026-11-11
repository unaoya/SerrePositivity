module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalSimplex

/-!
# 通常右余錐の有限単体表示

概要：元の余錐を有限単体へ制限し、最後の頂点に元の余錐頂点を置く。
方針：同じ宇宙の ULift 順序添字に制限して終点拡張を適用する。
規約：元の通常余錐の join 写像と厳密に一致する。
使われ方：native roof prism の零端。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open CategoryTheory Limits SSet MonoidalCategory
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}
  (c : Cocone F) {n : ℕ} (Γ : Fin (n + 1) ⥤ I)

def lifted : ULift.{u} (Fin (n + 1)) ⥤ I :=
  (⟨ULift.down, fun _ _ h => h⟩ : ULift.{u} (Fin (n + 1)) →o Fin (n + 1)).toFunctor ⋙ Γ

def diagram : Fin (n + 2) ⥤ C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.index n ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWithTerminalFunctor (c.whisker (lifted Γ))

lemma diagram_obj_cast (i : Fin (n + 1)) :
    (diagram c Γ).obj i.castSucc = F.obj (Γ.obj i) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWithTerminalFunctor (c.whisker (lifted Γ))).obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.obj n i.castSucc) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.obj_cast]
  rfl

lemma diagram_obj_last : (diagram c Γ).obj (Fin.last (n + 1)) = c.pt := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWithTerminalFunctor (c.whisker (lifted Γ))).obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.obj n (Fin.last (n + 1))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.obj_last]
  rfl

lemma diagram_map_cast_cast (i j : Fin (n + 1)) (hij : i ≤ j) :
    HEq ((diagram c Γ).map (homOfLE (Fin.castSucc_le_castSucc_iff.mpr hij)))
      (F.map (Γ.map (homOfLE hij))) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.map_heq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWithTerminalFunctor (c.whisker (lifted Γ)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.obj_cast n i) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.obj_cast n j)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.index n).map (homOfLE (Fin.castSucc_le_castSucc_iff.mpr hij)))
    (WithTerminal.incl.map (homOfLE
      (show (ULift.up i : ULift.{u} (Fin (n + 1))) ≤ ULift.up j from hij)))

lemma diagram_map_cast_last (i : Fin (n + 1)) :
    HEq ((diagram c Γ).map (homOfLE (Fin.le_last i.castSucc))) (c.ι.app (Γ.obj i)) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.map_heq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWithTerminalFunctor (c.whisker (lifted Γ)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.obj_cast n i) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.obj_last n)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.index n).map (homOfLE (Fin.le_last i.castSucc)))
    (WithTerminal.homFrom (ULift.up i))

lemma lifted_nerve : (stdSimplex.isoNerve n).hom ≫ nerveMap (lifted Γ) =
    SSet.yonedaEquiv.symm (show (nerve I) _⦋n⦌ from Γ) := by
  rfl

lemma diagram_join :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫
      SSet.yonedaEquiv.symm (show (nerve C) _⦋n + 1⦌ from diagram c Γ) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm (show (nerve I) _⦋n⦌ from Γ))
      (𝟙 (Δ[0] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv c).val := by
  have h : SSet.yonedaEquiv.symm
      (show (nerve C) _⦋n + 1⦌ from diagram c Γ) =
      SSet.yonedaEquiv.symm
        (show (nerve _) _⦋n + 1⦌ from _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.index n) ≫
        nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWithTerminalFunctor (c.whisker (lifted Γ))) := by
    rfl
  rw [h, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.index_join, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCocone_withTerminal, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCocone_whisker]
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, lifted_nerve, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
