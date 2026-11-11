module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratedSourceTransport
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SquareDiagonal
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingSplitProjection
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiniteShapes
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSpanComparison
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseHorns
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitExistenceTransfer

/-!
概要：固定始域圏の終対象の終域へ向かう辺を、閉包内辺の pushout に沿って延長する。
方針：pushout の上辺を分裂させ、正方形の元のホモトピー可換式と合成する。
規約：結論は元のホモトピー圏での延長存在。写像空間全体の可縮性はまだ結論しない。
使われ方：HTT 5.5.5.14 の終対象から局所性への零次元の工程。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Truncated.HomotopyCategory

private lemma homMk_change_source {X : SSet.{u}} {x y z : X _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj X) x z)
    (f : Truncated.Edge (X := (truncation 2).obj X) y z)
    (h : x = y) (he : e.edge = f.edge) :
    eqToHom (congrArg (fun a ↦ (HomotopyCategory.mk a : hoFunctor.obj X)) h) ≫ homMk f =
      homMk e := by
  subst y
  have hef : e = f := Truncated.Edge.ext he
  rw [hef, eqToHom_refl, Category.id_comp]

/-- 指定 pushout の上辺が終対象の終域から出るなら、底辺に沿う元の写像を延長できる。 -/
lemma generatedSource_terminal_pushout_extension
    {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceCategory edges x) _⦋0⦌) (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex s)
    (R : (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ C) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R)
    (hbottom : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ R) ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges)
    (hy : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 1 = (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceTarget edges x).app _ s) :
    ∃ f : (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 1 0) : hoFunctor.obj C) ⟶
        HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 1),
      homMk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow R) ≫ f = homMk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftArrow R) := by
  have htop := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.stronglySaturatedClosure_stronglySaturated
    (SSet.uliftFunctor.{u + 1, u}).obj (Set.range edges)).2.1 R hR hbottom
  let u : C.Edge ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceTarget edges x).app _ s) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 1 1) :=
    { edge := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow R).edge
      src_eq := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow R).src_eq.trans hy
      tgt_eq := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow R).tgt_eq }
  have hu : u.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges := by
    change (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow R).edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareTopArrow_edge]
    exact htop
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSource_terminal_generatedEdge_isSplitMono edges x s hs u hu
  have hmove := homMk_change_source (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow R) u.toTruncated hy rfl
  have : IsSplitMono (homMk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow R)) := by
    rw [← hmove]
    infer_instance
  refine ⟨homMk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow R) ≫ retraction (homMk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow R)), ?_⟩
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomRight_homMk_diagonal,
    ← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareLeftTop_homMk_diagonal, Category.assoc, IsSplitMono.id, Category.comp_id]

private lemma extension_exists_of_edge_eq {C : SSet.{u}}
    {a b y a' b' y' : C _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj C) a b)
    (g : Truncated.Edge (X := (truncation 2).obj C) a y)
    (f' : Truncated.Edge (X := (truncation 2).obj C) a' b')
    (g' : Truncated.Edge (X := (truncation 2).obj C) a' y')
    (hf : f'.edge = f.edge) (hg : g'.edge = g.edge)
    (h : ∃ k : (HomotopyCategory.mk b' : hoFunctor.obj C) ⟶ HomotopyCategory.mk y',
      homMk f' ≫ k = homMk g') :
    ∃ k : (HomotopyCategory.mk b : hoFunctor.obj C) ⟶ HomotopyCategory.mk y,
      homMk f ≫ k = homMk g := by
  have ha : a' = a := f'.src_eq.symm.trans ((congrArg (C.δ 1) hf).trans f.src_eq)
  have hb : b' = b := f'.tgt_eq.symm.trans ((congrArg (C.δ 0) hf).trans f.tgt_eq)
  have hy : y' = y := g'.tgt_eq.symm.trans ((congrArg (C.δ 0) hg).trans g.tgt_eq)
  subst a'
  subst b'
  subst y'
  have hff : f' = f := Truncated.Edge.ext hf
  have hgg : g' = g := Truncated.Edge.ext hg
  simpa only [hff, hgg] using h

/-- 小余完備性から元の二辺の pushout を作り、指定した元の辺の延長を得る。 -/
lemma generatedSource_terminal_edge_extension
    {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceCategory edges x) _⦋0⦌) (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex s)
    {a b : C _⦋0⦌} (f : Truncated.Edge (X := (truncation 2).obj C) a b)
    (hf : f.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges)
    (g : Truncated.Edge (X := (truncation 2).obj C) a ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceTarget edges x).app _ s)) :
    ∃ k : (HomotopyCategory.mk b : hoFunctor.obj C) ⟶
        HomotopyCategory.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceTarget edges x).app _ s),
      homMk f ≫ k = homMk g := by
  let p := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f g
  let j := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso.{u, u + 1} 2 0).hom
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanHasColimit_iff_restrict_of_isIso p j).mpr
    exact hC (horn 2 0 : SSet.{u}) (j ≫ p)
  obtain ⟨c, hc⟩ := hp
  let R := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare c
  have hRf : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ R = SSet.yonedaEquiv.symm f.edge := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare_bottom, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan_left]
  have hRg : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ R = SSet.yonedaEquiv.symm g.edge := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare_left, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan_right]
  have hbottom : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ R) ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges := by
    rw [hRf]
    exact ((SSet.yonedaEquiv (X := C) (n := ⦋1⦌)).apply_symm_apply f.edge).symm ▸ hf
  have hy : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 1 = (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceTarget edges x).app _ s := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftEdge_target, hRg]
    exact (congrArg (C.δ 0)
      ((SSet.yonedaEquiv (X := C) (n := ⦋1⦌)).apply_symm_apply g.edge)).trans g.tgt_eq
  have h := generatedSource_terminal_pushout_extension edges x s hs R
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare_isPushout c hc) hbottom hy
  apply extension_exists_of_edge_eq f g (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow R) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftArrow R) ?_ ?_ h
  · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow_edge, hRf]
    exact (SSet.yonedaEquiv (X := C) (n := ⦋1⦌)).apply_symm_apply f.edge
  · rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareLeftArrow_edge, hRg]
    exact (SSet.yonedaEquiv (X := C) (n := ⦋1⦌)).apply_symm_apply g.edge

/-- 終対象の終域への前合成写像は、元のホモトピー圏の全射である。 -/
lemma generatedSource_terminal_precomp_surjective
    {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceCategory edges x) _⦋0⦌) (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex s)
    {a b : C _⦋0⦌} (f : Truncated.Edge (X := (truncation 2).obj C) a b)
    (hf : f.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges) :
    Function.Surjective (fun k : (HomotopyCategory.mk b : hoFunctor.obj C) ⟶
        HomotopyCategory.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceTarget edges x).app _ s) ↦ homMk f ≫ k) := by
  intro g
  obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective a _ g
  exact generatedSource_terminal_edge_extension hC edges x s hs f hf e

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
