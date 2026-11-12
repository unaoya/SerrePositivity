module

public import SerrePositivity.KST.Comparison.TelescopeFunctor
public import SerrePositivity.KST.Comparison.SequenceHomotopyPullbacks
public import SerrePositivity.KST.Comparison.SimplicialSumHomotopyPullbacks
public import SerrePositivity.KST.Comparison.SpanGluing

/-!
# telescope のホモトピー引き戻しの貼り合わせ

概要：順序列の各遷移のホモトピー引き戻しから、各段階と telescope の四角形を得る。
方針：Kan な縦射の場合を余積と Lemma 1.7 から導き、関手的な Kan 分解で一般化する。
規約：Segal 1974 Lemma 1.8。結論を入力の構造体として仮定しない。
使われ方：Segal Proposition 1.6 の有限骨格から無限骨格への移行。
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
概要：縦射が Kan なら、隣接段の仮定は telescope の span の二面をホモトピー引き戻しにする。
方針：全ての遷移への帰納と、添字を写す余積のホモトピー引き戻しの保存を使う。
規約：偶数・奇数の二面を同時に述べる。
使われ方：Lemma 1.7 の仮定。
-/
theorem telescopeSpan_homotopyPullbacks_of_fibrations {F G : ℕ ⥤ SSet.{u}}
    (α : F ⟶ G) (hα : ∀ n, SSet.modelCategoryQuillen.J.rlp (α.app n))
    (h : ∀ n, IsHomotopyPullback
      (naturalitySquare (diagramArrow (homOfLE (Nat.le_succ n))) α)) :
    IsHomotopyPullback
      (naturalitySquare (diagramArrow WalkingSpan.Hom.fst) (telescopeSpanMap α)) ∧
    IsHomotopyPullback
      (naturalitySquare (diagramArrow WalkingSpan.Hom.snd) (telescopeSpanMap α)) := by
  constructor
  · exact simplicialSumReindex_homotopyPullback_of_fibrations
      (B := fun n => F.obj (2 * n)) (D := fun n => G.obj (2 * n)) telescopeEvenIndex
      (fun i => F.map (homOfLE (telescopeEdgeDegree_le_even i)))
      (fun i => α.app (telescopeEdgeDegree i)) (fun n => α.app (2 * n))
      (fun i => G.map (homOfLE (telescopeEdgeDegree_le_even i)))
      (fun _ => ⟨α.naturality _⟩)
      (fun i => sequenceArrow_homotopyPullback_of_successors α hα h
        (telescopeEdgeDegree_le_even i)) (fun n => hα (2 * n))
  · exact simplicialSumReindex_homotopyPullback_of_fibrations
      (B := fun n => F.obj (2 * n + 1)) (D := fun n => G.obj (2 * n + 1)) telescopeOddIndex
      (fun i => F.map (homOfLE (telescopeEdgeDegree_le_odd i)))
      (fun i => α.app (telescopeEdgeDegree i)) (fun n => α.app (2 * n + 1))
      (fun i => G.map (homOfLE (telescopeEdgeDegree_le_odd i)))
      (fun _ => ⟨α.naturality _⟩)
      (fun i => sequenceArrow_homotopyPullback_of_successors α hα h
        (telescopeEdgeDegree_le_odd i)) (fun n => hα (2 * n + 1))

/--
概要：Kan な縦射を持つ順序列の各偶数・奇数段と telescope の四角形はホモトピー引き戻しである。
方針：余積の二面へ Lemma 1.7 を使い、各成分の包含の四角形と横に貼り合わせる。
規約：隣接する四角形だけを仮定する。
使われ方：関手的な Kan 分解で一般の場合へ戻す際の中間の定理。
-/
theorem telescopeStages_homotopyPullback_of_fibrations {F G : ℕ ⥤ SSet.{u}}
    (α : F ⟶ G) (hα : ∀ n, SSet.modelCategoryQuillen.J.rlp (α.app n))
    (h : ∀ n, IsHomotopyPullback
      (naturalitySquare (diagramArrow (homOfLE (Nat.le_succ n))) α)) (n : ℕ) :
    IsHomotopyPullback (naturalitySquare (telescopeEvenStage n) α) ∧
    IsHomotopyPullback (naturalitySquare (telescopeOddStage n) α) := by
  obtain ⟨hL, hR⟩ := telescopeSpan_homotopyPullbacks_of_fibrations α hα h
  constructor
  · let hs := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_isPullback (fun k => α.app (2 * k)) n
    have hv := simplicialSumMap_rlp (fun k => α.app (2 * k)) (fun k => hα (2 * k))
    exact isHomotopyPullback_paste_horiz_of_middle_fibration hs.toCommSq
      (naturalitySquare spanCylinderLeft (telescopeSpanMap α))
      (isHomotopyPullback_of_left_fibration hs hv)
      (spanCylinder_vertex_homotopyPullback (telescopeSpanMap α) hL hR .left) hv
  · let hs := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_isPullback (fun k => α.app (2 * k + 1)) n
    have hv := simplicialSumMap_rlp (fun k => α.app (2 * k + 1)) (fun k => hα (2 * k + 1))
    exact isHomotopyPullback_paste_horiz_of_middle_fibration hs.toCommSq
      (naturalitySquare spanCylinderRight (telescopeSpanMap α))
      (isHomotopyPullback_of_left_fibration hs hv)
      (spanCylinder_vertex_homotopyPullback (telescopeSpanMap α) hL hR .right) hv

/--
概要：隣接段の自然性の四角形がホモトピー引き戻しなら、全ての段階と telescope の四角形もそうなる。
方針：順序列の射の Kan 分解、Lemma 1.7 と余積による貼り合わせ、単位による模型の不変性を使う。
規約：Segal 1974 Lemma 1.8。各対象の Kan 性や遷移射の単射性を追加しない。
使われ方：有限骨格から telescope を経る無限骨格への比較。
-/
theorem telescopeStages_homotopyPullback {F G : ℕ ⥤ SSet.{u}}
    (α : F ⟶ G)
    (h : ∀ n, IsHomotopyPullback
      (naturalitySquare (diagramArrow (homOfLE (Nat.le_succ n))) α)) (n : ℕ) :
    IsHomotopyPullback (naturalitySquare (telescopeEvenStage n) α) ∧
    IsHomotopyPullback (naturalitySquare (telescopeOddStage n) α) := by
  have hi d : IsIso (AnodyneHomotopy.anodyneQ.map ((diagramKanUnit α).app d)) :=
    Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
      (diagramKanUnit_anodyne α d)
  have ht := telescopeFunctor_map_localized_isIso (diagramKanUnit α) hi
  have hβ k := (diagramKan_arrowSquare_iff α (homOfLE (Nat.le_succ k))).mp (h k)
  obtain ⟨he, ho⟩ := telescopeStages_homotopyPullback_of_fibrations
    (diagramKanProjection α) (diagramKanProjection_rlp α) hβ n
  exact ⟨(naturalitySquare_factorization_iff (telescopeEvenStage n) α (diagramKanUnit α)
    (diagramKanProjection α) (diagramKan_fac α) (hi (2 * n)) ht).mpr he,
    (naturalitySquare_factorization_iff (telescopeOddStage n) α (diagramKanUnit α)
      (diagramKanProjection α) (diagramKan_fac α) (hi (2 * n + 1)) ht).mpr ho⟩

end SerrePositivity.KST.Comparison
