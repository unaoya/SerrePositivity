module

public import SerrePositivity.KST.Comparison.DiagramKanReplacement
public import SerrePositivity.KST.Comparison.AlternativeFiberCriterion

/-!
# 順序図式の厳密なファイバーへの比較

概要：図式の右縦射を分解し、各段階のホモトピー引き戻しを図式圏のファイバーへ比較する。
方針：図式圏の引き戻しの普遍性と、評価関手の引き戻し保存を使う。
規約：Segal 1974 Proposition 1.6 の無限骨格の段階の補助。
使われ方：成分ごとの局所化同型へ順序余極限の保存定理を適用する。
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
概要：順序図式の上左の対象から、下辺と Kan 射影の引き戻しへの比較。
方針：元の四角形と図式の分解の因子化の等式で引き戻しへ持ち上げる。
規約：引き戻しは図式圏での実際の極限。
使われ方：各段階と順序余極限で共通の比較を使う。
-/
def sequentialFiberComparison {A X Y B : ℕ ⥤ SSet.{u}}
    {a : A ⟶ X} {b : A ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B} (sq : CommSq a b f g) :
    A ⟶ pullback g (diagramKanProjection f) :=
  pullback.lift b (a ≫ diagramKanUnit f) (by
    rw [Category.assoc, diagramKan_fac]
    exact sq.w.symm)

/--
概要：各段階の四角形がホモトピー引き戻しなら、ファイバーへの比較も各段階で局所化同型。
方針：評価した厳密な引き戻しと、別分解の比較の判定を使う。
規約：図式の射の Kan 性や単射性は不要。
使われ方：ファイバー比較への順序余極限の局所化同型保存。
-/
theorem sequentialFiberComparison_app_localized_isIso {A X Y B : ℕ ⥤ SSet.{u}}
    {a : A ⟶ X} {b : A ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B} (sq : CommSq a b f g)
    (h : ∀ n, IsHomotopyPullback (CommSq.mk
      (congrArg (fun t => t.app n) sq.w))) (n : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((sequentialFiberComparison sq).app n)) := by
  let ev := (evaluation ℕ SSet.{u}).obj n
  have hpb := (IsPullback.of_hasPullback g (diagramKanProjection f)).map ev
  apply (isHomotopyPullback_iff_alternative_fiber
    (CommSq.mk (congrArg (fun t => t.app n) sq.w))
    ((diagramKanUnit f).app n)
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
      (diagramKanUnit_anodyne f n))
    ((diagramKanProjection f).app n) (diagramKanProjection_rlp f n)
    (congrArg (fun t => t.app n) (diagramKan_fac f)) hpb
    ((sequentialFiberComparison sq).app n) ?_ ?_).mp (h n)
  · exact congrArg (fun t => t.app n)
      (pullback.lift_fst (f := g) (g := diagramKanProjection f) b (a ≫ diagramKanUnit f) _)
  · exact congrArg (fun t => t.app n)
      (pullback.lift_snd (f := g) (g := diagramKanProjection f) b (a ≫ diagramKanUnit f) _)

end SerrePositivity.KST.Comparison
