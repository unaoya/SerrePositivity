module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceTransport
public import SerrePositivity.InfinityCategories.Stable.SquareDiagonal
public import SerrePositivity.InfinityCategories.Stable.PastingSplitProjection
public import SerrePositivity.InfinityCategories.Core.FiniteShapes
public import SerrePositivity.InfinityCategories.Stable.SuspensionSpanComparison
public import SerrePositivity.InfinityCategories.Core.UniverseHorns
public import SerrePositivity.InfinityCategories.Core.ColimitExistenceTransfer

/-!
概要：固定始域圏の終対象の終域へ向かう辺を、閉包内辺の pushout に沿って延長する。
方針：pushout の上辺を分裂させ、正方形の元のホモトピー可換式と合成する。
規約：結論は元のホモトピー圏での延長存在。写像空間全体の可縮性はまだ結論しない。
使われ方：HTT 5.5.5.14 の終対象から局所性への零次元の工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits Truncated.HomotopyCategory

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
    (s : (generatedSourceCategory edges x) _⦋0⦌) (hs : IsTerminalVertex s)
    (R : (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ C) (hR : IsPushoutSquare R)
    (hbottom : SSet.yonedaEquiv (squareBottomEdge ≫ R) ∈ generatedEdges edges)
    (hy : squareVertex R 0 1 = (generatedSourceTarget edges x).app _ s) :
    ∃ f : (HomotopyCategory.mk (squareVertex R 1 0) : hoFunctor.obj C) ⟶
        HomotopyCategory.mk (squareVertex R 0 1),
      homMk (squareBottomArrow R) ≫ f = homMk (squareLeftArrow R) := by
  have htop := (stronglySaturatedClosure_stronglySaturated
    (SSet.uliftFunctor.{u + 1, u}).obj (Set.range edges)).2.1 R hR hbottom
  let u : C.Edge ((generatedSourceTarget edges x).app _ s) (squareVertex R 1 1) :=
    { edge := (squareTopArrow R).edge
      src_eq := (squareTopArrow R).src_eq.trans hy
      tgt_eq := (squareTopArrow R).tgt_eq }
  have hu : u.edge ∈ generatedEdges edges := by
    change (squareTopArrow R).edge ∈ generatedEdges edges
    rw [squareTopArrow_edge]
    exact htop
  have := generatedSource_terminal_generatedEdge_isSplitMono edges x s hs u hu
  have hmove := homMk_change_source (squareTopArrow R) u.toTruncated hy rfl
  have : IsSplitMono (homMk (squareTopArrow R)) := by
    rw [← hmove]
    infer_instance
  refine ⟨homMk (squareRightArrow R) ≫ retraction (homMk (squareTopArrow R)), ?_⟩
  rw [← Category.assoc, squareBottomRight_homMk_diagonal,
    ← squareLeftTop_homMk_diagonal, Category.assoc, IsSplitMono.id, Category.comp_id]

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
    (hC : HasSmallColimits C) (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (generatedSourceCategory edges x) _⦋0⦌) (hs : IsTerminalVertex s)
    {a b : C _⦋0⦌} (f : Truncated.Edge (X := (truncation 2).obj C) a b)
    (hf : f.edge ∈ generatedEdges edges)
    (g : Truncated.Edge (X := (truncation 2).obj C) a ((generatedSourceTarget edges x).app _ s)) :
    ∃ k : (HomotopyCategory.mk b : hoFunctor.obj C) ⟶
        HomotopyCategory.mk ((generatedSourceTarget edges x).app _ s),
      homMk f ≫ k = homMk g := by
  let p := edgeSpan f g
  let j := (uliftHornIso.{u, u + 1} 2 0).hom
  have hp : HasColimit p := by
    apply (F1B.kanHasColimit_iff_restrict_of_isIso p j).mpr
    exact hC (horn 2 0 : SSet.{u}) (j ≫ p)
  obtain ⟨c, hc⟩ := hp
  let R := coconeSquare c
  have hRf : squareBottomEdge ≫ R = SSet.yonedaEquiv.symm f.edge := by
    rw [coconeSquare_bottom, edgeSpan_left]
  have hRg : squareLeftEdge ≫ R = SSet.yonedaEquiv.symm g.edge := by
    rw [coconeSquare_left, edgeSpan_right]
  have hbottom : SSet.yonedaEquiv (squareBottomEdge ≫ R) ∈ generatedEdges edges := by
    rw [hRf]
    exact ((SSet.yonedaEquiv (X := C) (n := ⦋1⦌)).apply_symm_apply f.edge).symm ▸ hf
  have hy : squareVertex R 0 1 = (generatedSourceTarget edges x).app _ s := by
    rw [← squareLeftEdge_target, hRg]
    exact (congrArg (C.δ 0)
      ((SSet.yonedaEquiv (X := C) (n := ⦋1⦌)).apply_symm_apply g.edge)).trans g.tgt_eq
  have h := generatedSource_terminal_pushout_extension edges x s hs R
    (coconeSquare_isPushout c hc) hbottom hy
  apply extension_exists_of_edge_eq f g (squareBottomArrow R) (squareLeftArrow R) ?_ ?_ h
  · rw [squareBottomArrow_edge, hRf]
    exact (SSet.yonedaEquiv (X := C) (n := ⦋1⦌)).apply_symm_apply f.edge
  · rw [squareLeftArrow_edge, hRg]
    exact (SSet.yonedaEquiv (X := C) (n := ⦋1⦌)).apply_symm_apply g.edge

/-- 終対象の終域への前合成写像は、元のホモトピー圏の全射である。 -/
lemma generatedSource_terminal_precomp_surjective
    {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}
    (hC : HasSmallColimits C) (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (generatedSourceCategory edges x) _⦋0⦌) (hs : IsTerminalVertex s)
    {a b : C _⦋0⦌} (f : Truncated.Edge (X := (truncation 2).obj C) a b)
    (hf : f.edge ∈ generatedEdges edges) :
    Function.Surjective (fun k : (HomotopyCategory.mk b : hoFunctor.obj C) ⟶
        HomotopyCategory.mk ((generatedSourceTarget edges x).app _ s) ↦ homMk f ≫ k) := by
  intro g
  obtain ⟨e, rfl⟩ := homotopyCategory_homMk_surjective a _ g
  exact generatedSource_terminal_edge_extension hC edges x s hs f hf e

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
