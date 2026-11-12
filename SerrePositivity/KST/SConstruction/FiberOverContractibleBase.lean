module
public import SerrePositivity.KST.SConstruction.PointedContractibility
public import SerrePositivity.KST.SConstruction.LocalizedTrivialFibrations
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationComparison

/-! # 可縮な底の上の Kan fiber の包含
概要：可縮な Kan 複体を底とする Kan fibration の fiber 包含は全基点 π_* 同型。
方針：底を終対象へ写す可換四角形に L9 の fiber 比較定理を適用する。
規約：全空間の可縮性は要求しない。使われ方：経路による homotopy fiber と loop の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits HomotopicalAlgebra SSet
open SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open Spectra
open scoped Simplicial

/-- 概要：終対象への射の fiber 包含は実際の同型。
方針：終対象から自身への基点射は同型であり、その引き戻しも同型。
規約：全空間の Kan 性は不要。使われ方：底を一点へ写す fiber 比較。 -/
lemma fiberTerminalInclusion_isIso (E : SSet.{u}) (e : E _⦋0⦌) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (terminal.from E) ((terminal.from E).app _ e)) := by
  let c := SSet.const (X := terminal SSet.{u}) ((terminal.from E).app _ e)
  have hc : c = 𝟙 (terminal SSet.{u}) := terminal.hom_ext _ _
  let : IsIso c := by rw [hc]; infer_instance
  change IsIso (pullback.fst (terminal.from E) c)
  infer_instance

/-- 概要：可縮な底の上の Kan fibration の fiber 包含は全基点 π_* 同型。
方針：全空間を固定して底を終対象へ写し、fiber 比較と終対象上の fiber の同型を合成する。
規約：零次数を含み、fiber の全ての基点で検証する。使われ方：homotopy fiber への loop の包含。 -/
lemma fiberInclusion_piIsomorphism_of_contractible_base {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan B) (e : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) := by
  let : KanComplex (terminal SSet.{u}) := by
    change Fibration (terminal.from (terminal SSet.{u}))
    have ht : terminal.from (terminal SSet.{u}) = 𝟙 (terminal SSet.{u}) := terminal.hom_ext _ _
    rw [ht]
    infer_instance
  let q := terminal.from E
  let g := terminal.from B
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration g := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_iff_trivialKanFibration B).1 hB
  have hg : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism g := kanPiIsomorphism_of_localized_isIso g
    (map_isIso_of_trivialKanFibration AnodyneHomotopy.anodyneQ
      (Localization.inverts AnodyneHomotopy.anodyneQ anodyneExtensions) g)
  have hw : p ≫ g = 𝟙 E ≫ q := terminal.hom_ext _ _
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberMap_piIsomorphism p q (𝟙 E) g hw
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.id E) hg e
  let : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι q (q.app _ e)) := fiberTerminalInclusion_isIso E e
  have hq : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι q (q.app _ e)) :=
    kanPiIsomorphism_of_localized_isIso _ (by infer_instance)
  have hc := h.comp hq
  have hfac : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap p q (𝟙 E) g hw e ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι q (q.app _ e) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap_ι p q (𝟙 E) g hw e).trans (Category.comp_id _)
  exact hfac ▸ hc

end SerrePositivity.KST.SConstruction
