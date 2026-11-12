module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.SimplexAttachmentFamilies
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.BoundaryEdgeLifting
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiniteShapes

/-!
概要：前段と次辺の指定比較を、両端と共有点の全経路を保持して全図式の比較へ延長する。
方針：実境界上へ比較辺を貼り、元の両端間の辺を自明 Kan 制限に沿って持ち上げる。
規約：制限は辺の類ではなく元の一次単体そのものに一致する。
使われ方：c5 の全有限線型図式の商比較の帰納的な貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- 前段と次辺の指定比較は、共有経路を変えず元の全図式間の一つの実比較辺へ貼れる。 -/
lemma exists_simplexAttachmentComparison {X : SSet.{u}} [Quasicategory X] (n : ℕ)
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0] ⟶ X)
    (a : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[n] Δ[0] ≫ F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[n] Δ[0] ≫ G)))
    (b : Truncated.Edge
      (X := (truncation 2).obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) Δ[0])).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]) ≫ F))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]) ≫ G)))
    (hab : SSet.yonedaEquiv.symm a.edge ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app X =
      SSet.yonedaEquiv.symm b.edge ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[0])).app X) :
    ∃ l : Truncated.Edge
      (X := (truncation 2).obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G),
      ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app X).app (Opposite.op ⦋1⦌) l.edge =
        a.edge ∧
      ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app X).app (Opposite.op ⦋1⦌)
        l.edge = b.edge := by
  let T := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentFamilyGlue n (SSet.yonedaEquiv.symm a.edge)
    (SSet.yonedaEquiv.symm b.edge) hab
  let p := (pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n).ι).app X
  have hp : p ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentPrefix n)).app X =
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app X := by
    rw [← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentPrefix_ι]
  have hbnd : p ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentLastEdge n)).app X =
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app X := by
    rw [← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentLastEdge_ι]
  have h0 : stdSimplex.δ (1 : Fin 2) ≫ T =
      SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPullback_pre_of_isPushout (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary_isPushout n) X).hom_ext
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentFamilyGlue_prefix, ← SSet.yonedaEquiv_symm_comp,
        Category.assoc, hp, SSet.yonedaEquiv_symm_comp]
      change stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm a.edge =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[n] Δ[0] ≫ F))
      exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_source a
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentFamilyGlue_lastEdge, ← SSet.yonedaEquiv_symm_comp,
        Category.assoc, hbnd, SSet.yonedaEquiv_symm_comp]
      change stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm b.edge =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]) ≫ F))
      exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_source b
  have h1 : stdSimplex.δ (0 : Fin 2) ≫ T =
      SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPullback_pre_of_isPushout (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary_isPushout n) X).hom_ext
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentFamilyGlue_prefix, ← SSet.yonedaEquiv_symm_comp,
        Category.assoc, hp, SSet.yonedaEquiv_symm_comp]
      change stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm a.edge =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[n] Δ[0] ≫ G))
      exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_target a
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentFamilyGlue_lastEdge, ← SSet.yonedaEquiv_symm_comp,
        Category.assoc, hbnd, SSet.yonedaEquiv_symm_comp]
      change stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm b.edge =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]) ≫ G))
      exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_target b
  let t : Truncated.Edge
      (X := (truncation 2).obj ((ihom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n : SSet.{u})).obj X))
      (p.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F))
      (p.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) := {
    edge := SSet.yonedaEquiv T
    src_eq := by
      change ((ihom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n : SSet.{u})).obj X).δ 1
        (SSet.yonedaEquiv T) = _
      rw [← stdSimplex.yonedaEquiv_δ_comp, h0, Equiv.apply_symm_apply]
    tgt_eq := by
      change ((ihom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n : SSet.{u})).obj X).δ 0
        (SSet.yonedaEquiv T) = _
      rw [← stdSimplex.yonedaEquiv_δ_comp, h1, Equiv.apply_symm_apply] }
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := p) (boundary 1).ι inferInstance
  obtain ⟨l, hl⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_edge_lift_of_boundary_one p (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) t
  refine ⟨l, ?_, ?_⟩
  · have he := congrArg (fun e =>
      ((pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentPrefix n)).app X).app (Opposite.op ⦋1⦌) e.edge) hl
    have hT := congrArg SSet.yonedaEquiv
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentFamilyGlue_prefix n (SSet.yonedaEquiv.symm a.edge)
        (SSet.yonedaEquiv.symm b.edge) hab)
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hT
    have hc := ConcreteCategory.congr_hom (C := Type u)
      (NatTrans.congr_app hp (Opposite.op ⦋1⦌)) l.edge
    change ((pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentPrefix n)).app X).app (Opposite.op ⦋1⦌)
      (p.app (Opposite.op ⦋1⦌) l.edge) = _ at hc
    change ((pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentPrefix n)).app X).app (Opposite.op ⦋1⦌)
      (p.app (Opposite.op ⦋1⦌) l.edge) =
        ((pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentPrefix n)).app X).app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv T) at he
    exact hc.symm.trans (he.trans hT)
  · have he := congrArg (fun e =>
      ((pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentLastEdge n)).app X).app (Opposite.op ⦋1⦌) e.edge) hl
    have hT := congrArg SSet.yonedaEquiv
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentFamilyGlue_lastEdge n (SSet.yonedaEquiv.symm a.edge)
        (SSet.yonedaEquiv.symm b.edge) hab)
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hT
    have hc := ConcreteCategory.congr_hom (C := Type u)
      (NatTrans.congr_app hbnd (Opposite.op ⦋1⦌)) l.edge
    change ((pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentLastEdge n)).app X).app (Opposite.op ⦋1⦌)
      (p.app (Opposite.op ⦋1⦌) l.edge) = _ at hc
    change ((pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentLastEdge n)).app X).app (Opposite.op ⦋1⦌)
      (p.app (Opposite.op ⦋1⦌) l.edge) =
        ((pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentLastEdge n)).app X).app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv T) at he
    exact hc.symm.trans (he.trans hT)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_simplexAttachmentComparison := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.exists_simplexAttachmentComparison
