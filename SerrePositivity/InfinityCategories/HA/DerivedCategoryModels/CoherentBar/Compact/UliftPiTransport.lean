module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.UliftPiNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Homotopy
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
/-!
概要：指定辺をたどる球面円柱の基点移送を宇宙とともに持ち上げる。
方針：元の円柱を持ち上げ、標準単体の宇宙同型で前合成する。
規約：指定辺も元の辺の持ち上げそのものとする。
使われ方：追加宇宙の全基点チャートを元の native 評価空間へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory MonoidalCategory SSet
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable {X : SSet.{u}} [KanComplex X]

lemma dgBarCompactPiTransport_ulift (n : ℕ) {x y : X _⦋0⦌} (e : X.Edge x y)
    {a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x} {b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n y}
    (h : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiTransport n e a b) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiTransport n
      (SSet.Edge.ofTruncated (X := (SSet.uliftFunctor.{v, u}).obj X)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, v} e.toTruncated))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPiEquiv.{u, v} X n x a)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPiEquiv.{u, v} X n y b) := by
  obtain ⟨f, g, hf, hg, H, hH⟩ := h
  let H' := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftSimplicialHomotopy.{u, v} H)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} (n + 1)).inv
  refine ⟨_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPointedSimplexUp f, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPointedSimplexUp g,
    ?_, ?_, H', ?_⟩
  · exact congrArg (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPiEquiv.{u, v} X n x) hf
  · exact congrArg (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPiEquiv.{u, v} X n y) hg
  · ext d s
    have h₀ := congrArg (fun q => q.app d
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftBoundarySimplexDown.{u, v} (n + 1) d s.1, ULift.up s.2.down)) hH
    exact congrArg ULift.up h₀

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
