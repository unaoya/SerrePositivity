module
public import SerrePositivity.KST.SConstruction.ZeroRowLoopTerminalFactor
public import SerrePositivity.KST.SConstruction.ZeroRowPointedLoopComparison

/-! # 元の零行 loop の Kan 延長の全基点 π 同型
概要：元の具体的 loop 射を既存の Kan 単位へ延長した射は正の全反復で全基点 π 同型。
方針：元の fiber 比較との厳密な分解で合成の同型性を移し、実際の loop 包含を打ち消す。
規約：零段基点と元の Kan 延長を保つ。使われ方：元の構造射の随伴の Ω 条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 元の零行 loop の Kan 延長と fiber 包含の合成は全基点 π 同型。 -/
lemma zeroRowKanLoopComparison_terminalComposite_piIsomorphism (r : ℕ) (X : StableModel.{u})
    (b : ((iteratedSRealizationDiagram (r + 1) X).obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((zeroRowKanLoopComparison (r + 1) X b).right ≫
      (loopToTerminalPathHomotopyFiber
        (pointedFullIteratedPathKanBoundary (r + 1) X)).right) := by
  let Q := AnodyneHomotopy.anodyneQ
  let i := PointedKanReplacement.unit.app (zeroRowPointedModel (r + 1) X b)
  let k := zeroRowKanLoopComparison (r + 1) X b
  let j := loopToTerminalPathHomotopyFiber (pointedFullIteratedPathKanBoundary (r + 1) X)
  have hi : IsIso (Q.map i.right) :=
    (Localization.inverts Q anodyneExtensions) _
      (PointedKanReplacement.unit_anodyne (zeroRowPointedModel (r + 1) X b))
  have hf : i.right ≫ k.right = zeroRowLoopComparison (r + 1) X :=
    congrArg Under.Hom.right (zeroRowKanLoopComparison_unit (r + 1) X b)
  have he : Q.map i.right ≫ Q.map (k.right ≫ j.right) =
      Q.map (zeroRowLoopComparison (r + 1) X ≫ j.right) := by
    rw [← Q.map_comp, ← Category.assoc, hf]
  have hr : IsIso (Q.map (zeroRowLoopComparison (r + 1) X ≫ j.right)) :=
    zeroRowLoopComparison_terminalComposite_localized_isIso r X
  have hc : IsIso (Q.map i.right ≫ Q.map (k.right ≫ j.right)) := he.symm ▸ hr
  exact kanPiIsomorphism_of_localized_isIso (k.right ≫ j.right)
    ((isIso_comp_left_iff _ _).mp hc)

/-- 元の具体的 loop 比較の既存の Kan 延長は、正の全反復で全基点 π 同型。 -/
lemma zeroRowKanLoopComparison_piIsomorphism (r : ℕ) (X : StableModel.{u})
    (b : ((iteratedSRealizationDiagram (r + 1) X).obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (zeroRowKanLoopComparison (r + 1) X b).right :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp
    (zeroRowKanLoopComparison_terminalComposite_piIsomorphism r X b)
    (loopToTerminalPathHomotopyFiber_piIsomorphism
      (pointedFullIteratedPathKanBoundary (r + 1) X)
      (pointedIteratedPathKan_isContractibleKan (r + 1) X))

end SerrePositivity.KST.SConstruction
