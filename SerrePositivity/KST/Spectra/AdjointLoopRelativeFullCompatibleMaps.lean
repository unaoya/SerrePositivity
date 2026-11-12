module

public import SerrePositivity.KST.Spectra.AdjointLoopRelativeParameterBoundary
public import SerrePositivity.KST.Spectra.RawSpectrumRelativeCorner

/-!
概要：元の単位の左右因子を同時に保つ、元の射と相対 BF 置換射の全 Hom。
方針：元の Hom の普遍パラメータ族の二境界へ実 corner を引き戻す。
規約：左因子だけの可換性から右射影の自然性を推論しない。
使われ方：指定単位・右射影を保つ全 Hom の実自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 概要：元の BF 全 Hom の同じ普遍パラメータ列射。
方針：元の Hom 上の恒等族を既存の全列対応で読む。
規約：元の Hom を別模型へ置き換えない。
使われ方：全 Hom を一度に扱う指定境界。 -/
def universalParameterHom (X Y : OmegaSpectrum.{u}) :
    KanSequence.Hom X.toKanSequence
      (KanSequence.mapping (RawSpectrumMapping.pointedSpace X Y.toKanSequence) Y.toKanSequence) :=
  RawSpectrumMapping.homOfParameterFamily X Y.toKanSequence _ (𝟙 _)

/-- 概要：元の全 Hom の普遍族から、元の左右因子を同時に指定する corner 境界。
方針：実構成した二つの全パラメータ境界と厳密可換性を使う。
規約：二境界の存在・可換性を追加入力に残さない。
使われ方：実 corner の全 Hom 上の引き戻し。 -/
def fullBoundaryMap (X Y : OmegaSpectrum.{u}) :
    mappingSpace X Y ⟶ RawSpectrumMapping.relativeCornerTarget (inclusion X) (projection Y) :=
  pullback.lift
    (inclusionParameterFamily X Y _ (universalParameterHom X Y)).right
    (projectionParameterFamily X Y _ (universalParameterHom X Y)).right (by
      have h := congrArg Under.Hom.right
        (parameterFamilyBoundary_comm X Y _ (universalParameterHom X Y))
      simp only [Under.comp_right] at h
      exact h.symm)

/-- 概要：指定二境界の第一射影は元の左因子の族。
方針：実引き戻しへの持ち上げの射影式を使う。
規約：元の Hom パラメータを保持する。
使われ方：全 Hom の左境界の回収。 -/
@[reassoc (attr := simp)]
lemma fullBoundaryMap_fst (X Y : OmegaSpectrum.{u}) :
    fullBoundaryMap X Y ≫ pullback.fst _ _ =
      (inclusionParameterFamily X Y _ (universalParameterHom X Y)).right :=
  pullback.lift_fst _ _ _

/-- 概要：指定二境界の第二射影は元の右射影先の族。
方針：実引き戻しへの持ち上げの射影式を使う。
規約：同じ Hom パラメータを保持する。
使われ方：全 Hom の右境界の回収。 -/
@[reassoc (attr := simp)]
lemma fullBoundaryMap_snd (X Y : OmegaSpectrum.{u}) :
    fullBoundaryMap X Y ≫ pullback.snd _ _ =
      (projectionParameterFamily X Y _ (universalParameterHom X Y)).right :=
  pullback.lift_snd _ _ _

/-- 概要：元の左右因子を同時に保つ元の射と置換射の組の実全空間。
方針：元の全 Hom の二境界へ実 corner 写像を引き戻す。
規約：対象ごとの選択から自然性を仮定しない。
使われ方：両境界を保持する全 Hom の回収。 -/
def fullCompatibleSpace (X Y : OmegaSpectrum.{u}) : SSet.{u} :=
  pullback (RawSpectrumMapping.relativeCorner (inclusion X) (projection Y)) (fullBoundaryMap X Y)

/-- 概要：両境界を保つ組から置換後の元の射を取り出す。
方針：実引き戻しの第一射影を使う。
規約：元の BF 全 Hom への射。
使われ方：置換後の全パラメータ族。 -/
def fullReplacedMap (X Y : OmegaSpectrum.{u}) :
    fullCompatibleSpace X Y ⟶ mappingSpace (middle X) (middle Y) :=
  pullback.fst _ _

/-- 概要：両境界を保つ組から元の射を取り出す。
方針：実引き戻しの第二射影を使う。
規約：元の全 Hom を保持する。
使われ方：元の族と指定左右因子の同時回収。 -/
def fullOriginalMap (X Y : OmegaSpectrum.{u}) :
    fullCompatibleSpace X Y ⟶ mappingSpace X Y :=
  pullback.snd _ _

/-- 概要：元の全 Hom への射影は両境界を固定しても実自明 Kan fibration。
方針：元の相対左因子と右射影の corner の全単射 RLP を引き戻す。
規約：指定境界の充填を仮定しない。
使われ方：元の全族を厳密に回収する比較。 -/
lemma fullOriginalMap_trivialKanFibration (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (fullOriginalMap X Y) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.of_isPullback
    (IsPullback.of_hasPullback
      (RawSpectrumMapping.relativeCorner (inclusion X) (projection Y)) (fullBoundaryMap X Y))
    (RawSpectrumMapping.relativeCorner_trivialKanFibration
      (inclusion X) (inclusion_relative X) (projection Y) (projection_rlp Y)).mem⟩

/-- 概要：両境界を保つ実全空間は Kan。
方針：元の Kan Hom への実自明 Kan fibration と終対象射を合成する。
規約：全空間の Kan 性を追加入力にしない。
使われ方：全図式比較の局所 Kan 条件。 -/
instance fullCompatibleSpace_kanComplex (X Y : OmegaSpectrum.{u}) :
    KanComplex (fullCompatibleSpace X Y) := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (fullOriginalMap X Y) := fullOriginalMap_trivialKanFibration X Y
  let : HomotopicalAlgebra.Fibration (fullOriginalMap X Y) :=
    (SSet.modelCategoryQuillen.fibration_iff _).2
      (fun _ _ j hj ↦ (fullOriginalMap_trivialKanFibration X Y).mem j
        (SSet.modelCategoryQuillen.J_le_monomorphisms j hj))
  change HomotopicalAlgebra.Fibration (terminal.from (fullCompatibleSpace X Y))
  rw [show terminal.from (fullCompatibleSpace X Y) =
    fullOriginalMap X Y ≫ terminal.from (mappingSpace X Y) from terminal.hom_ext _ _]
  infer_instance

/-- 概要：元の全 Hom は両境界を保つ組から実際に同値として回収される。
方針：元の射への自明 Kan fibration を順射に持つ同値を使う。
規約：この段階で組の豊穣合成の法則までは主張しない。
使われ方：全 Hom 自然性の指定左右境界を保つ比較。 -/
def fullOriginalEquivalence (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (fullCompatibleSpace X Y) (mappingSpace X Y) := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (fullOriginalMap X Y) := fullOriginalMap_trivialKanFibration X Y
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (fullOriginalMap X Y)

/-- 概要：組から回収した置換射は指定左因子を全 Hom 上で厳密に保つ。
方針：実引き戻しの可換式を corner の第一射影へ制限する。
規約：元の二境界の一方を別の族へ変えない。
使われ方：元の単位の左因子の自然性。 -/
@[reassoc] lemma fullCompatible_left_condition (X Y : OmegaSpectrum.{u}) :
    fullReplacedMap X Y ≫ RawSpectrumMapping.pre (inclusion X) (middle Y).toKanSequence =
      fullOriginalMap X Y ≫
        (inclusionParameterFamily X Y _ (universalParameterHom X Y)).right := by
  dsimp only [fullReplacedMap, fullOriginalMap, fullCompatibleSpace]
  have h := congrArg (· ≫ pullback.fst _ _) (pullback.condition
    (f := RawSpectrumMapping.relativeCorner (inclusion X) (projection Y))
    (g := fullBoundaryMap X Y))
  simpa only [Category.assoc, RawSpectrumMapping.relativeCorner_fst,
    fullBoundaryMap_fst] using h

/-- 概要：同じ置換射は指定右射影も全 Hom 上で厳密に保つ。
方針：同じ実引き戻しの可換式を corner の第二射影へ制限する。
規約：左右因子の自然性を同じ組の空間で保持する。
使われ方：元の単位と右射影の全 Hom 比較。 -/
@[reassoc] lemma fullCompatible_right_condition (X Y : OmegaSpectrum.{u}) :
    fullReplacedMap X Y ≫ RawSpectrumMapping.post (middle X) (projection Y) =
      fullOriginalMap X Y ≫
        (projectionParameterFamily X Y _ (universalParameterHom X Y)).right := by
  dsimp only [fullReplacedMap, fullOriginalMap, fullCompatibleSpace]
  have h := congrArg (· ≫ pullback.snd _ _) (pullback.condition
    (f := RawSpectrumMapping.relativeCorner (inclusion X) (projection Y))
    (g := fullBoundaryMap X Y))
  simpa only [Category.assoc, RawSpectrumMapping.relativeCorner_snd,
    fullBoundaryMap_snd] using h

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
