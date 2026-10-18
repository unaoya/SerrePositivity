module
public import SerrePositivity.KST.SConstruction.KSequenceMaps
public import SerrePositivity.KST.Spectra.CofibrantSequenceLifting

/-! # 単射構造射を持つ K の候補列の比較射
概要：入力の射から、単射構造射を持つ K の候補列間の厳密な射を作る。
方針：厳密化済みの射を標的の置換射影に沿って逐次的に持ち上げる。
規約：恒等・合成の厳密な関手法則はここでは主張しない。使われ方：K の関手性への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra.PointedMapping

/-- 概要：K の候補列の置換射影は各段で全ての単射への RLP を持つ。
方針：L9 の逐次置換の段に保存された持ち上げ性を取り出す。
規約：底の単体集合の射。使われ方：列の射の標的の置換への持ち上げ。 -/
lemma monicKKanSequenceProjection_rlp (X : StableModel.{u}) (r : ℕ) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      ((monicKKanSequenceProjection X).app r).right :=
  (Spectra.KanSequence.replacementStage (kKanSequence X) r).projection_rlp

/-- 概要：入力の射から作る単射構造射の K の候補列間の厳密な射。
方針：源の構造射の単射性と標的の置換射影の RLP により逐次的に持ち上げる。
規約：Ω 条件は使わない。使われ方：K のスペクトル射への接続。 -/
def monicKKanSequenceMap {X Y : StableModel.{u}} (f : X ⟶ Y) :
    Spectra.KanSequence.Hom (monicKKanSequence X) (monicKKanSequence Y) :=
  Spectra.KanSequence.liftHom (monicKKanSequence_sigma_mono X)
    (monicKKanSequenceProjection Y) (monicKKanSequenceProjection_rlp Y) (monicKToRawMap f)

/-- 概要：持ち上げた射は標的の置換射影との合成で厳密化済みの射を回収する。
方針：L9 の列の持ち上げの比較式を使う。
規約：全段の厳密等号。使われ方：元の反復 S の写像との照合。 -/
lemma monicKKanSequenceMap_projection {X Y : StableModel.{u}} (f : X ⟶ Y) (r : ℕ) :
    (monicKKanSequenceMap f).app r ≫ (monicKKanSequenceProjection Y).app r =
      (monicKToRawMap f).app r :=
  Spectra.KanSequence.liftHom_fac _ _ _ _ r

/-- 概要：持ち上げた射は射影との合成後で元の入力の射と同じ成分を表す。
方針：持ち上げの厳密な比較と、厳密化で保持された成分の等式をつなぐ。
規約：零段を含む全段。使われ方：置換した K の射の各段のホモトピー比較。 -/
lemma monicKKanSequenceMap_projection_component {X Y : StableModel.{u}} (f : X ⟶ Y) (r : ℕ) :
    componentOf ((monicKKanSequenceMap f).app r ≫ (monicKKanSequenceProjection Y).app r) =
      componentOf ((monicKKanSequenceProjection X).app r ≫ kKanSequenceLevelMap f r) := by
  rw [monicKKanSequenceMap_projection]
  exact monicKToRawMap_component f r

end SerrePositivity.KST.SConstruction
