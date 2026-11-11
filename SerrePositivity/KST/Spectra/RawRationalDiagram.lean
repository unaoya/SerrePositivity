module

public import SerrePositivity.KST.Spectra.RationalSpectrumDiagram
public import SerrePositivity.KST.Spectra.FilteredKanSequenceForgetful
public import SerrePositivity.KST.Spectra.FilteredKanSequenceMap

/-!
概要：置換前の Kan 内部 Hom 列による有理 telescope の厳密な図式。
方針：円の次数射の前合成を並べ、元のスペクトルの射は後合成で作用させる。
規約：前合成と後合成の可換性は厳密。BF 比較は別に持ち上げる。
使われ方：BF 1978 §2、HA §1.4.2。有理化の実際の射の自然性。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：内部 Hom の Kan 列を円の次数射でつないだ自然数の図式。
方針：次数 2,3,4,… の前合成を隣接射とする。
規約：cofibrant 置換前の図式。
使われ方：BF 1978 §2。厳密に関手的な telescope の入力。 -/
def rawRationalSequence (X : OmegaSpectrum.{u}) : ℕ ⥤ KanSequence.{u} :=
  Functor.ofSequence (X := fun _ : ℕ ↦ KanSequence.mapping CirclePower.space.{u} X.toKanSequence)
    (fun n ↦ KanSequence.mappingPre (CirclePower.powerMap (n + 2)) X.toKanSequence)

/-- 概要：内部 Hom の Kan 列の有理化図式の universe を揃える。
方針：AsSmall の忘却を前合成する。
規約：filtered Kan 余極限への入力。
使われ方：BF 1978 §2、HA §1.4.2。有理化の自然性。 -/
def rawRationalDiagram (X : OmegaSpectrum.{u}) : AsSmall.{u} ℕ ⥤ KanSequence.{u} :=
  AsSmall.down ⋙ rawRationalSequence X

/-- 概要：置換前の有理化図式は各対象で Ω 条件を満たす。
方針：内部 Hom の Ω 条件の保存を使う。
規約：構造射の単射性は仮定しない。
使われ方：BF 1978 §2。余極限列の BF 置換。 -/
theorem rawRationalDiagram_omega (X : OmegaSpectrum.{u}) (a : AsSmall.{u} ℕ) :
    ((rawRationalDiagram X).obj a).OmegaCondition :=
  KanSequence.mapping_omegaCondition CirclePower.space.{u} X.toKanSequence X.toKanSequence_omega

/-- 概要：元のスペクトルの射は置換前の有理化図式の厳密な自然変換を与える。
方針：各段の後合成が円の次数射の前合成と可換することを使う。
規約：隣接射の可換性から全ての射の可換性を得る。
使われ方：BF 1978 §2、HA §1.4.2。実際の telescope の射。 -/
def rawRationalSequenceMap {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    rawRationalSequence X ⟶ rawRationalSequence Y :=
  NatTrans.ofSequence (fun _ ↦ KanSequence.mappingPost CirclePower.space.{u}
    (⟨f.app, f.comm⟩)) (fun n ↦ by
      dsimp only [rawRationalSequence]
      rw [Functor.ofSequence_map_homOfLE_succ, Functor.ofSequence_map_homOfLE_succ]
      apply KanSequence.Hom.ext_app
      intro k
      change _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed _ _ ≫ (ihom CirclePower.space.{u}).map (f.app k) =
        (ihom CirclePower.space.{u}).map (f.app k) ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed _ _
      simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
      exact MonoidalClosed.pre_comm_ihom_map _ _)

/-- 概要：universe を揃えた有理化図式に射を作用させる。
方針：厳密な自然変換に AsSmall の忘却を前合成する。
規約：成分は各段の内部 Hom の後合成。
使われ方：BF 1978 §2、HA §1.4.2。filtered BF 比較射への入力。 -/
def rawRationalDiagramMap {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    rawRationalDiagram X ⟶ rawRationalDiagram Y :=
  Functor.whiskerLeft AsSmall.down (rawRationalSequenceMap f)

/-- 概要：既存の cotensor の図式から置換前の内部 Hom 列への自然変換。
方針：各段に単射置換の射影を使い、次数射との比較式を適用する。
規約：置換の持ち上げの選択によらず、この正方形は厳密。
使われ方：BF 1978 §2、HTT A.3.3。既存の有理化対象との比較。 -/
def rationalSequenceProjection (X : OmegaSpectrum.{u}) :
    rationalSequence X ⋙ forgetToKan ⟶ rawRationalSequence X :=
  NatTrans.ofSequence (fun _ ↦ cotensorProjection CirclePower.space.{u} X)
    (fun n ↦ by
      apply KanSequence.Hom.ext_app
      intro k
      change (((rationalSequence X).map (homOfLE (n.le_add_right 1))).app k) ≫
        (cotensorProjection CirclePower.space.{u} X).app k =
        (cotensorProjection CirclePower.space.{u} X).app k ≫
          (((rawRationalSequence X).map (homOfLE (n.le_add_right 1))).app k)
      dsimp only [rationalSequence, rawRationalSequence]
      rw [Functor.ofSequence_map_homOfLE_succ, Functor.ofSequence_map_homOfLE_succ]
      exact cotensorPre_comparison _ X k)

/-- 概要：既存の有理化図式から内部 Hom の Kan 列の図式への比較。
方針：自然数の比較に AsSmall の忘却を前合成する。
規約：全ての成分は各段で全基点 π_* 同型。
使われ方：BF 1978 §2、HA §1.4.2。有理化対象の置換不変性。 -/
def rationalDiagramProjection (X : OmegaSpectrum.{u}) :
    rationalDiagram X ⋙ forgetToKan ⟶ rawRationalDiagram X :=
  Functor.whiskerLeft AsSmall.down (rationalSequenceProjection X)

/-- 概要：有理化図式の比較は各段で全基点 π_* 同型。
方針：cotensor の単射置換の比較の性質を取り出す。
規約：零次数を含む。
使われ方：Goerss–Jardine I §7、BF 1978 §2。filtered 比較の同型性。 -/
theorem rationalDiagramProjection_levelwise (X : OmegaSpectrum.{u})
    (a : AsSmall.{u} ℕ) (k : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (((rationalDiagramProjection X).app a).app k).right :=
  cotensorProjection_piIsomorphism CirclePower.space.{u} X k

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
