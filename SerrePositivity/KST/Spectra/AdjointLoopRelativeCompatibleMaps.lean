module

public import SerrePositivity.KST.Spectra.AdjointLoopRelativeBF
public import SerrePositivity.KST.Spectra.RawSpectrumPreWhitehead
public import SerrePositivity.KST.Spectra.PullbackKanSequence
public import SerrePositivity.KST.NonConnective.SequentialRelativeHomFibration
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.KanFibrationEquivalence

/-!
概要：補助単位の相対 BF 左因子と厳密可換な、全 Hom の組を構成する。
方針：左因子への制限が自明 Kan fibration であることを実証し、後合成へ引き戻す。
規約：選択した置換を通常の関手と仮定しない。nativeLoop との比較は含めない。
使われ方：相対 BF 置換の源の全 Hom と指定単位を同時に保持する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 概要：元の単位の相対左因子による全 Hom の制限は自明 Kan fibration。
方針：相対 latching 単射性による fibration と実 BF 同値によるホモトピー逆を使う。
規約：一般 Kan 列を標的とする元の制限射そのもの。
使われ方：全 Hom の自然な組の源射影の充填。 -/
lemma inclusionPre_trivialKanFibration (X : OmegaSpectrum.{u}) (Z : KanSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (RawSpectrumMapping.pointedPre (inclusion X) Z).right := by
  let : Fibration (RawSpectrumMapping.pre (inclusion X) Z) :=
    SerrePositivity.KST.NonConnective.sequentialRawHomPre_fibration
      (inclusion X) (inclusion_relative X) Z
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.trivialKanFibration_of_fibration_of_simplicialHomotopyEquivalence
    (RawSpectrumMapping.pre (inclusion X) Z)
    (RawSpectrumMapping.pre_homotopyEquivalence_of_levelwise
      (inclusion X) (inclusion_levelwise X) Z)

/-- 概要：元の全 Hom から相対 BF 左因子への後合成。
方針：元の左因子の段射と構造可換式を使う。
規約：源の全 Hom パラメータを維持する。
使われ方：左因子と可換な組の引き戻しの底辺。 -/
def inclusionPost (X Y : OmegaSpectrum.{u}) :
    RawSpectrumMapping.pointedSpace X Y.toKanSequence ⟶
      RawSpectrumMapping.pointedSpace X (middle Y).toKanSequence :=
  RawSpectrumMapping.pointedPost X
    (⟨(inclusion Y).app, (inclusion Y).comm⟩ :
      KanSequence.Hom Y.toKanSequence (middle Y).toKanSequence)

/-- 概要：相対 BF 左因子と厳密可換な元の射と置換射の組の全空間。
方針：元の二つの全 Hom の射の実引き戻しを取る。
規約：点ごとのホモトピー類の組で代用しない。
使われ方：相対置換の coherent な自然性を構成する Hom。 -/
def compatibleSpace (X Y : OmegaSpectrum.{u}) : PointedSimplicialSet.{u} :=
  pullback (RawSpectrumMapping.pointedPre (inclusion X) (middle Y).toKanSequence)
    (inclusionPost X Y)

/-- 概要：可換な組から置換後の射を取り出す射影。
方針：実引き戻しの第一射影を使う。
規約：全単体上の点つき射。
使われ方：置換後の全 Hom への比較。 -/
def replacedMap (X Y : OmegaSpectrum.{u}) : compatibleSpace X Y ⟶
    RawSpectrumMapping.pointedSpace (middle X) (middle Y).toKanSequence :=
  pullback.fst _ _

/-- 概要：可換な組から元の射を取り出す射影。
方針：実引き戻しの第二射影を使う。
規約：元の BF 全 Hom を保持する。
使われ方：置換前の全 Hom との比較。 -/
def originalMap (X Y : OmegaSpectrum.{u}) : compatibleSpace X Y ⟶
    RawSpectrumMapping.pointedSpace X Y.toKanSequence :=
  pullback.snd _ _

/-- 概要：二射影は元の相対 BF 左因子と全パラメータで厳密可換。
方針：引き戻しの可換式を取り出す。
規約：指定単位の左因子を変えない。
使われ方：全図式の自然性を保つ境界条件。 -/
@[reassoc] lemma compatible_condition (X Y : OmegaSpectrum.{u}) :
    replacedMap X Y ≫
      RawSpectrumMapping.pointedPre (inclusion X) (middle Y).toKanSequence =
        originalMap X Y ≫ inclusionPost X Y :=
  pullback.condition

/-- 概要：元の全 Hom への射影は実際に自明 Kan fibration。
方針：相対左因子への全 Hom 制限の全単射 RLP を引き戻す。
規約：比較の存在や充填を明示入力に残さない。
使われ方：元の射と可換な置換射の全族回収。 -/
lemma originalMap_trivialKanFibration (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (originalMap X Y).right :=
  ⟨_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_snd_rlp _ _ (inclusionPre_trivialKanFibration X _).mem⟩

/-- 概要：可換な組の元の全空間は Kan。
方針：実射影の自明 Kan fibration と元の Hom の Kan 性を使う。
規約：Hom の Kan 性を新たに仮定しない。
使われ方：coherent nerve へ進むための全 Hom 条件。 -/
instance compatibleSpace_kanComplex (X Y : OmegaSpectrum.{u}) :
    KanComplex (compatibleSpace X Y).right := by
  let t := inclusionPre_trivialKanFibration X (middle Y).toKanSequence
  let : Fibration
      (RawSpectrumMapping.pointedPre (inclusion X) (middle Y).toKanSequence).right :=
    (modelCategoryQuillen.fibration_iff _).2
      (fun _ _ j hj ↦ t.mem j (modelCategoryQuillen.J_le_monomorphisms j hj))
  exact _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_kanComplex _ _

/-- 概要：可換な組と元の BF Hom は実際に同値。
方針：元の射への自明 Kan fibration を順射とする同値を使う。
規約：選択した置換射を関手にするとは主張しない。
使われ方：全図式比較に必要な Hom の回収。 -/
def originalEquivalence (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (compatibleSpace X Y).right (mappingSpace X Y) := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (originalMap X Y).right :=
    originalMap_trivialKanFibration X Y
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (originalMap X Y).right

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
