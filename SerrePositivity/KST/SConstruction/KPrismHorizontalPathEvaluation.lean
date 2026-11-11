module
public import SerrePositivity.KST.SConstruction.CoherentPrismHorizontalFaces
public import SerrePositivity.KST.SConstruction.CoherentOuterFacePaths
public import SerrePositivity.KST.SConstruction.CoherentPathActionConstancy
public import SerrePositivity.KST.SConstruction.KPrismSliceDiagrams

/-! # 元の K prism の水平 Path 作用は全次数で定数
概要：元の上下の水平作用が、全 Path の全次数で定数であることを証明する。
方針：元の水平面を strict 図式に同定し、全射な外側面から元の Hom 作用へ戻す。
規約：元の豊穣単体を保持し、Kan の充填や追加の同値入力を要しない。
使われ方：上下の円柱の終点を元の水平射と構造射の二合成に照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open Spectra SerrePositivity.InfinityCategories
open scoped Simplicial
local instance kPrismHorizontalPathEvaluation_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 下側の元の水平 Hom 作用の値は、全次数で入力 Path に依存しない。 -/
lemma kKanOriginalPrismLowerHorizontalValues_eq {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} {f : x ⟶ y}
    (s : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) (d : ℕ)
    (P Q : (nerve (SimplicialThickening.Path (ULift.up (0 : Fin (s.length + 1)).castSucc : ULift.{u} (Fin (s.length + 2)))
      (ULift.up (Fin.last s.length).castSucc))) _⦋d⦌) :
    let R : EnrichedFunctor SSet.{u}
      (SimplicialThickening (ULift.{u} (Fin (s.length + 2)))) PointedSimplicialSet.{u} :=
    (kKanOriginalPrismStringDiagram r F).app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString s).chain)
    (R.map (.mk (ULift.up (0 : Fin (s.length + 1)).castSucc)) (.mk (ULift.up (Fin.last s.length).castSucc))).app
      (Opposite.op ⦋d⦌) P =
      (R.map (.mk (ULift.up (0 : Fin (s.length + 1)).castSucc)) (.mk (ULift.up (Fin.last s.length).castSucc))).app
        (Opposite.op ⦋d⦌) Q := by
  let R : EnrichedFunctor SSet.{u}
      (SimplicialThickening (ULift.{u} (Fin (s.length + 2)))) PointedSimplicialSet.{u} :=
    (kKanOriginalPrismStringDiagram r F).app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString s).chain)
  have hc : coherentPathActionsConstant
      ((SimplicialThickening.functor (SimplexCategory.δ (Fin.last (s.length + 1))).toOrderHom.uliftMap).comp
        SSet R) := by
    have hr := coherentLowerPrismString_rawHorizontalCell (kKanOriginalPrismStringDiagram r F) s
    have hs := congrArg (fun Q => Q.app (Opposite.op ⦋s.length⦌) (ULift.up s.chain))
      (kKanOriginalPrismStringDiagram_bottom r F)
    exact (congrArg coherentPathActionsConstant (hr.trans hs)).mpr
      (coherentStrictDiagramPathActionsConstant _ _)
  have h := coherentPathValues_eq_of_epi
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap.{u} (Fin.last (s.length + 1)) 0 (Fin.last s.length))
    (R.map (.mk (ULift.up ((Fin.last (s.length + 1)).succAbove 0)))
      (.mk (ULift.up ((Fin.last (s.length + 1)).succAbove (Fin.last s.length)))))
    (fun n p q => hc (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last s.length))) n p q)
  have h' : ∀ (n : ℕ) (p q : (nerve (SimplicialThickening.Path
      (ULift.up (0 : Fin (s.length + 1)).castSucc : ULift.{u} (Fin (s.length + 2))) (ULift.up (Fin.last s.length).castSucc))) _⦋n⦌),
      (R.map (.mk (ULift.up (0 : Fin (s.length + 1)).castSucc)) (.mk (ULift.up (Fin.last s.length).castSucc))).app (Opposite.op ⦋n⦌) p =
        (R.map (.mk (ULift.up (0 : Fin (s.length + 1)).castSucc)) (.mk (ULift.up (Fin.last s.length).castSucc))).app (Opposite.op ⦋n⦌) q := by
    let V (a b : Fin (s.length + 2)) : Prop :=
      ∀ (n : ℕ) (p q : (nerve (SimplicialThickening.Path
          (ULift.up a : ULift.{u} (Fin (s.length + 2))) (ULift.up b))) _⦋n⦌),
        (R.map (.mk (ULift.up a)) (.mk (ULift.up b))).app (Opposite.op ⦋n⦌) p =
          (R.map (.mk (ULift.up a)) (.mk (ULift.up b))).app (Opposite.op ⦋n⦌) q
    have hV : V ((Fin.last (s.length + 1)).succAbove 0)
        ((Fin.last (s.length + 1)).succAbove (Fin.last s.length)) := h
    exact (congrArg₂ V (Fin.succAbove_last_apply (0 : Fin (s.length + 1)))
      (Fin.succAbove_last_apply (Fin.last s.length))).mp hV
  exact h' d P Q

/-- 上側の元の水平 Hom 作用の値は、全次数で入力 Path に依存しない。 -/
lemma kKanOriginalPrismUpperHorizontalValues_eq {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} {f : x ⟶ y}
    (s : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) (d : ℕ)
    (P Q : (nerve (SimplicialThickening.Path (ULift.up (0 : Fin (s.length + 1)).succ : ULift.{u} (Fin (s.length + 2)))
      (ULift.up (Fin.last s.length).succ))) _⦋d⦌) :
    let R : EnrichedFunctor SSet.{u}
      (SimplicialThickening (ULift.{u} (Fin (s.length + 2)))) PointedSimplicialSet.{u} :=
    (kKanOriginalPrismStringDiagram r F).app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString s).chain)
    (R.map (.mk (ULift.up (0 : Fin (s.length + 1)).succ)) (.mk (ULift.up (Fin.last s.length).succ))).app
      (Opposite.op ⦋d⦌) P =
      (R.map (.mk (ULift.up (0 : Fin (s.length + 1)).succ)) (.mk (ULift.up (Fin.last s.length).succ))).app
        (Opposite.op ⦋d⦌) Q := by
  let R : EnrichedFunctor SSet.{u}
      (SimplicialThickening (ULift.{u} (Fin (s.length + 2)))) PointedSimplicialSet.{u} :=
    (kKanOriginalPrismStringDiagram r F).app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString s).chain)
  have hc : coherentPathActionsConstant
      ((SimplicialThickening.functor (SimplexCategory.δ (0 : Fin (s.length + 2))).toOrderHom.uliftMap).comp
        SSet R) := by
    have hr := coherentUpperPrismString_rawHorizontalCell (kKanOriginalPrismStringDiagram r F) s
    have hs := congrArg (fun Q => Q.app (Opposite.op ⦋s.length⦌) (ULift.up s.chain))
      (kKanOriginalPrismStringDiagram_top r F)
    exact (congrArg coherentPathActionsConstant (hr.trans hs)).mpr
      (coherentStrictDiagramPathActionsConstant _ _)
  have h := coherentPathValues_eq_of_epi
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap.{u} (0 : Fin (s.length + 2)) 0 (Fin.last s.length))
    (R.map (.mk (ULift.up ((0 : Fin (s.length + 2)).succAbove 0)))
      (.mk (ULift.up ((0 : Fin (s.length + 2)).succAbove (Fin.last s.length)))))
    (fun n p q => hc (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last s.length))) n p q)
  have h' : ∀ (n : ℕ) (p q : (nerve (SimplicialThickening.Path
      (ULift.up (0 : Fin (s.length + 1)).succ : ULift.{u} (Fin (s.length + 2))) (ULift.up (Fin.last s.length).succ))) _⦋n⦌),
      (R.map (.mk (ULift.up (0 : Fin (s.length + 1)).succ)) (.mk (ULift.up (Fin.last s.length).succ))).app (Opposite.op ⦋n⦌) p =
        (R.map (.mk (ULift.up (0 : Fin (s.length + 1)).succ)) (.mk (ULift.up (Fin.last s.length).succ))).app (Opposite.op ⦋n⦌) q := by
    exact h
  exact h' d P Q

end SerrePositivity.KST.SConstruction
