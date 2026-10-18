module

public import SerrePositivity.KST.Comparison.AlternativePullback
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# 直積のホモトピー引き戻し

概要：任意のファイバーを持つ直積の四角形がホモトピー引き戻しとなることを示す。
方針：ファイバーだけを Kan 置換した別の分解で比較射を計算する。
規約：Segal 1974 Proposition 1.6 の bar の各行の積座標。元のファイバーの Kan 性は不要。
使われ方：パラメータ付き平行移動の可逆性を行のホモトピー引き戻し性へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.SimplicialModel

/--
概要：左変数を変える直積の標準四角形は厳密な引き戻しである。
方針：二つの射影の普遍性で持ち上げと一意性を確認する。
規約：Segal 1974 Proposition 1.6 の積座標。
使われ方：Kan 置換したファイバーでの標準比較の同型。
-/
theorem productPullbackSquare {X Y : SSet.{u}} (f : X ⟶ Y) (Z : SSet.{u}) :
    IsPullback (fst X Z) (f ▷ Z) f (fst Y Z) := by
  refine IsPullback.mk' (by rfl) ?_ ?_
  · intro W a b hfst hprod
    apply CartesianMonoidalCategory.hom_ext
    · exact hfst
    · have h := congrArg (fun k => k ≫ snd Y Z) hprod
      simpa only [Category.assoc, whiskerRight_snd] using h
  · intro W a b h
    refine ⟨lift a (b ≫ snd Y Z), lift_fst _ _, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerRight_fst, ← Category.assoc, lift_fst]
      exact h
    · rw [Category.assoc, whiskerRight_snd, lift_snd]

/--
概要：Kan なファイバーを持つ直積の第一射影は Kan fibration である。
方針：終射の Kan 条件を直積の普遍性で引き戻す。
規約：Segal 1974 Proposition 1.6 の各行の射影。基底の Kan 性は不要。
使われ方：ファイバーのみを置換した分解の右射。
-/
theorem productProjection_rlp (X Y : SSet.{u}) [SSet.KanComplex Y] :
    SSet.modelCategoryQuillen.J.rlp (fst X Y) := by
  let : (fibrations SSet.{u}).IsStableUnderBaseChange := by
    rw [fibrations_eq]
    infer_instance
  let : (fibrations SSet.{u}).RespectsIso := by
    rw [fibrations_eq]
    infer_instance
  have hy : Fibration (toUnit Y) :=
    (isFibrant_iff_of_isTerminal (toUnit Y) isTerminalTensorUnit).mp inferInstance
  have hs : IsPullback (fst X Y) (snd X Y) (toUnit X) (toUnit Y) :=
    IsPullback.of_isLimit_binaryFan_of_isTerminal (tensorProductIsBinaryProduct X Y)
      isTerminalTensorUnit
  rw [← fibrations_eq]
  exact (fibrations SSet.{u}).of_isPullback hs.flip ((HomotopicalAlgebra.fibration_iff _).mp hy)

/--
概要：horn の小対象論法による置換の値は Kan 複体である。
方針：終射の右持ち上げ性を Kan 条件へ移す。
規約：Segal 1974 Proposition 1.6 のファイバーの置換。値宇宙のモデル構造は仮定しない。
使われ方：直積の別の Kan 分解。
-/
theorem kanReplacement_kan (X : SSet.{u}) :
    SSet.KanComplex (AnodyneKanReplacement.functor.obj X) := by
  change Fibration (terminal.from (AnodyneKanReplacement.functor.obj X))
  exact (SSet.modelCategoryQuillen.fibration_iff _).mpr (AnodyneKanReplacement.terminal_rlp X)

/--
概要：任意のファイバーを持つ直積の標準四角形はホモトピー引き戻しである。
方針：ファイバーだけの Kan 置換による分解を選び、比較射を置換の直積と同型の合成にする。
規約：Segal 1974 Proposition 1.6。元の単体的モノイドの Kan 性は要求しない。
使われ方：bar の各行のホモトピー引き戻し比較の基準四角形。
-/
theorem productPullback_isHomotopyPullback {X Y : SSet.{u}} (f : X ⟶ Y) (Z : SSet.{u}) :
    IsHomotopyPullback (productPullbackSquare f Z).toCommSq := by
  let R := AnodyneKanReplacement.functor.obj Z
  let e := AnodyneKanReplacement.unit.app Z
  let i := Y ◁ e
  let p := fst Y R
  have hi : SSet.anodyneExtensions i := (AnodyneKanReplacement.unit_anodyne Z).whiskerLeft Y
  let : SSet.KanComplex R := kanReplacement_kan Z
  have hp : SSet.modelCategoryQuillen.J.rlp p := productProjection_rlp Y R
  have h : i ≫ p = fst Y Z := whiskerLeft_fst _ _
  apply (isHomotopyPullback_iff_alternative (productPullbackSquare f Z).toCommSq i hi p hp h).mpr
  let c := (productPullbackSquare f R).isoPullback
  have hfac : alternativePullbackComparison (productPullbackSquare f Z).toCommSq i p h =
      X ◁ e ≫ c.hom := by
    apply pullback.hom_ext
    · rw [alternativePullbackComparison_fst, Category.assoc,
        (productPullbackSquare f R).isoPullback_hom_fst, whiskerLeft_fst]
      rfl
    · rw [alternativePullbackComparison_snd, Category.assoc,
        (productPullbackSquare f R).isoPullback_hom_snd]
      exact (whisker_exchange f e).symm
  have : IsIso (AnodyneHomotopy.anodyneQ.map (X ◁ e)) :=
    Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
      ((AnodyneKanReplacement.unit_anodyne Z).whiskerLeft X)
  rw [hfac, AnodyneHomotopy.anodyneQ.map_comp]
  infer_instance

end SerrePositivity.KST.Comparison
