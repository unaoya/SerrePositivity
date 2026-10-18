module

public import SerrePositivity.KST.Comparison.SequentialFiberComparison
public import SerrePositivity.KST.Comparison.SequentialKanColimit
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanSequentialColimitComparison

/-!
# 単射な順序図式のホモトピー引き戻しの余極限

概要：各段階でホモトピー引き戻しである順序図式の四角形を余極限へ移す。
方針：右縦射を関手的に分解し、厳密なファイバーの比較と有限極限の交換を使う。
規約：Segal 1974 Proposition 1.6 の無限骨格への段階。原典の telescope と異なり
horn の有限表示可能性と実際の順序余極限による証明を使う。
使われ方：有限骨格の各行の比較から fat realization 全体の比較を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SerrePositivity.SimplicialModel

/--
概要：各段階のホモトピー引き戻しの四角形の余極限もホモトピー引き戻し。
方針：分解の単位とファイバーへの比較の余極限を局所化同型にし、Kan 射影で判定する。
規約：単射性は上側二つの図式の一段階の遷移だけに要求する。
使われ方：無限骨格の行の比較。
-/
theorem sequential_homotopyPullback {A X Y B : ℕ ⥤ SSet.{u}}
    {a : A ⟶ X} {b : A ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B} (sq : CommSq a b f g)
    (hA : ∀ n, Mono (SequentialBoundaryFactorization.stepMap A n))
    (hX : ∀ n, Mono (SequentialBoundaryFactorization.stepMap X n))
    (h : ∀ n, IsHomotopyPullback (CommSq.mk (congrArg (fun t => t.app n) sq.w))) :
    IsHomotopyPullback ((colim : (ℕ ⥤ SSet.{u}) ⥤ SSet.{u}).map_commSq sq) := by
  let i := diagramKanUnit f
  let p := diagramKanProjection f
  let k := sequentialFiberComparison sq
  have hi : IsIso (AnodyneHomotopy.anodyneQ.map (colim.map i)) :=
    KanSequentialColimitComparison.localized_isIso i hX (fun n =>
      Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
        (diagramKanUnit_anodyne f n))
  have hk : IsIso (AnodyneHomotopy.anodyneQ.map (colim.map k)) :=
    KanSequentialColimitComparison.localized_isIso k hA
      (sequentialFiberComparison_app_localized_isIso sq h)
  have hp : SSet.modelCategoryQuillen.J.rlp (colim.map p) :=
    sequentialColim_rlp p (diagramKanProjection_rlp f)
  have hfac : colim.map i ≫ colim.map p = colim.map f := by
    rw [← Functor.map_comp]
    exact congrArg (fun t => colim.map t) (diagramKan_fac f)
  have hpb := (IsPullback.of_hasPullback g p).map
    (colim : (ℕ ⥤ SSet.{u}) ⥤ SSet.{u})
  apply (isHomotopyPullback_iff_alternative_fiber
    ((colim : (ℕ ⥤ SSet.{u}) ⥤ SSet.{u}).map_commSq sq)
    (colim.map i) hi (colim.map p) hp hfac hpb (colim.map k) ?_ ?_).mpr hk
  · rw [← Functor.map_comp]
    exact congrArg (fun t => colim.map t)
      (pullback.lift_fst (f := g) (g := p) b (a ≫ i) _)
  · rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun t => colim.map t)
      (pullback.lift_snd (f := g) (g := p) b (a ≫ i) _)

end SerrePositivity.KST.Comparison
