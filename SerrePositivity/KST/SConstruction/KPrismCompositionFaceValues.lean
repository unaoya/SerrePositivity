module
public import SerrePositivity.KST.SConstruction.KPrismHorizontalPathEvaluation
public import SerrePositivity.KST.SConstruction.CoherentAdjacentPathEvaluation
public import SerrePositivity.KST.SConstruction.CoherentCompositionFaceConstancy

/-! # 元の K prism の上下の合成面の全次数での定数性
概要：元の上下の合成面で、全高次 Path の値が元の同じ二合成の値に限られることを証明する。
方針：水平作用の定数性と隣接縦辺の Path の一意性を、元の豊穣合成則で束ねる。
規約：元の K の豊穣単体と全次数を保持し、Kan の充填を選ばない。
使われ方：全精密化パラメータ上の上下の円柱の終点を定数族として回収する。
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
local instance kPrismCompositionFaceValues_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 下側の元の合成面の値は、全次数で切断点を通る Path に依存しない。 -/
lemma kKanOriginalPrismLowerCompositionValues_eq {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} {f : x ⟶ y}
    (s : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) (d : ℕ)
    (P Q : (nerve (SimplicialThickening.Path
      (ULift.up 0 : ULift.{u} (Fin (s.length + 2)))
      (ULift.up (Fin.last (s.length + 1))))) _⦋d⦌)
    (hP : P ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up (Fin.last s.length).castSucc)).obj (Opposite.op ⦋d⦌))
    (hQ : Q ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up (Fin.last s.length).castSucc)).obj (Opposite.op ⦋d⦌)) :
    let R : EnrichedFunctor SSet.{u}
        (SimplicialThickening (ULift.{u} (Fin (s.length + 2)))) PointedSimplicialSet.{u} :=
      (kKanOriginalPrismStringDiagram r F).app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString s).chain)
    (R.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (s.length + 1))))).app
      (Opposite.op ⦋d⦌) P =
      (R.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (s.length + 1))))).app
        (Opposite.op ⦋d⦌) Q := by
  let R : EnrichedFunctor SSet.{u}
      (SimplicialThickening (ULift.{u} (Fin (s.length + 2)))) PointedSimplicialSet.{u} :=
    (kKanOriginalPrismStringDiagram r F).app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString s).chain)
  refine coherentCompositionFaceValues_eq R
    (show (ULift.up 0 : ULift.{u} (Fin (s.length + 2))) ≤ ULift.up (Fin.last s.length).castSucc from Fin.zero_le _)
    (show ULift.up (Fin.last s.length).castSucc ≤ ULift.up (Fin.last (s.length + 1)) from Fin.le_last _) ?_ ?_ d P Q hP hQ
  · exact kKanOriginalPrismLowerHorizontalValues_eq r F s
  · exact coherentAdjacentPathValues_eq (Fin.last s.length) _

/-- 上側の元の合成面の値は、全次数で切断点を通る Path に依存しない。 -/
lemma kKanOriginalPrismUpperCompositionValues_eq {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} {f : x ⟶ y}
    (s : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) (d : ℕ)
    (P Q : (nerve (SimplicialThickening.Path
      (ULift.up 0 : ULift.{u} (Fin (s.length + 2)))
      (ULift.up (Fin.last (s.length + 1))))) _⦋d⦌)
    (hP : P ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up ((0 : Fin (s.length + 1)).succ))).obj (Opposite.op ⦋d⦌))
    (hQ : Q ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up ((0 : Fin (s.length + 1)).succ))).obj (Opposite.op ⦋d⦌)) :
    let R : EnrichedFunctor SSet.{u}
        (SimplicialThickening (ULift.{u} (Fin (s.length + 2)))) PointedSimplicialSet.{u} :=
      (kKanOriginalPrismStringDiagram r F).app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString s).chain)
    (R.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (s.length + 1))))).app
      (Opposite.op ⦋d⦌) P =
      (R.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (s.length + 1))))).app
        (Opposite.op ⦋d⦌) Q := by
  let R : EnrichedFunctor SSet.{u}
      (SimplicialThickening (ULift.{u} (Fin (s.length + 2)))) PointedSimplicialSet.{u} :=
    (kKanOriginalPrismStringDiagram r F).app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString s).chain)
  refine coherentCompositionFaceValues_eq R
    (show (ULift.up 0 : ULift.{u} (Fin (s.length + 2))) ≤ ULift.up ((0 : Fin (s.length + 1)).succ) from Fin.zero_le _)
    (show ULift.up ((0 : Fin (s.length + 1)).succ) ≤ ULift.up (Fin.last (s.length + 1)) from Fin.le_last _) ?_ ?_ d P Q hP hQ
  · exact coherentAdjacentPathValues_eq (0 : Fin (s.length + 1)) _
  · exact kKanOriginalPrismUpperHorizontalValues_eq r F s

/-- 元の両端へ移送した下側の native Hom の値も、合成面の全 Path で一致する。 -/
lemma kKanOriginalPrismLowerNativeValues_eq {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} {f : x ⟶ y}
    (s : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) (d : ℕ)
    (P Q : (nerve (SimplicialThickening.Path
      (ULift.up 0 : ULift.{u} (Fin (s.length + 2)))
      (ULift.up (Fin.last (s.length + 1))))) _⦋d⦌)
    (hP : P ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up (Fin.last s.length).castSucc)).obj (Opposite.op ⦋d⦌))
    (hQ : Q ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up (Fin.last s.length).castSucc)).obj (Opposite.op ⦋d⦌)) :
    (coherentStringNativeMap (kKanOriginalPrismStringDiagram r F)
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString s)).app (Opposite.op ⦋d⦌) P =
      (coherentStringNativeMap (kKanOriginalPrismStringDiagram r F)
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString s)).app (Opposite.op ⦋d⦌) Q := by
  dsimp only [coherentStringNativeMap, coherentStringDiagramCell, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.reobjectFunctor]
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
  congr 2
  exact kKanOriginalPrismLowerCompositionValues_eq r F s d P Q hP hQ

/-- 元の両端へ移送した上側の native Hom の値も、合成面の全 Path で一致する。 -/
lemma kKanOriginalPrismUpperNativeValues_eq {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} {f : x ⟶ y}
    (s : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) (d : ℕ)
    (P Q : (nerve (SimplicialThickening.Path
      (ULift.up 0 : ULift.{u} (Fin (s.length + 2)))
      (ULift.up (Fin.last (s.length + 1))))) _⦋d⦌)
    (hP : P ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up ((0 : Fin (s.length + 1)).succ))).obj (Opposite.op ⦋d⦌))
    (hQ : Q ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up ((0 : Fin (s.length + 1)).succ))).obj (Opposite.op ⦋d⦌)) :
    (coherentStringNativeMap (kKanOriginalPrismStringDiagram r F)
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString s)).app (Opposite.op ⦋d⦌) P =
      (coherentStringNativeMap (kKanOriginalPrismStringDiagram r F)
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString s)).app (Opposite.op ⦋d⦌) Q := by
  dsimp only [coherentStringNativeMap, coherentStringDiagramCell, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.reobjectFunctor]
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
  congr 2
  exact kKanOriginalPrismUpperCompositionValues_eq r F s d P Q hP hQ

end SerrePositivity.KST.SConstruction
