module

public import SerrePositivity.KST.Spectra.AdjointLoopRelativeBF
public import SerrePositivity.KST.Spectra.RawSpectrumRelativeCorner
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber

/-!
概要：相対 BF 右射影への比較を、指定した左右境界を保つ全パラメータ族として構成する。
方針：二変数 corner を同じ二境界へ引き戻し、全単射 RLP と可縮な選択 fiber を回収する。
規約：固定 BF 始点に対する補題。実 loop 始点の存在や動く始点の豊穣合成は主張しない。
使われ方：d3b② の比較射 c の境界付き相対充填。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.NonConnective
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 同じ補助標的への右射影と、固定した相対左因子の比較 corner。 -/
abbrev comparisonCorner (X : OmegaSpectrum.{u}) {A L : OmegaSpectrum.{u}} (a : A ⟶ L) :=
  RawSpectrumMapping.relativeCorner a (projection X)

/-- 実 BF 右射影の RLP と相対左因子から、比較 corner 自身の RLP を得る。 -/
lemma comparisonCorner_trivialKanFibration (X : OmegaSpectrum.{u})
    {A L : OmegaSpectrum.{u}} (a : A ⟶ L) (ha : IsSequentialRelativeCofibration a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (comparisonCorner X a) :=
  RawSpectrumMapping.relativeCorner_trivialKanFibration a ha (projection X) (projection_rlp X)

/-- 比較射の二つの指定境界を全パラメータ上で同時に記憶する空間。 -/
def comparisonResolution (X : OmegaSpectrum.{u}) {A L : OmegaSpectrum.{u}} (a : A ⟶ L)
    {U : SSet.{u}} (b : U ⟶ RawSpectrumMapping.relativeCornerTarget a (projection X)) :
    SSet.{u} :=
  pullback (comparisonCorner X a) b

/-- 比較射を忘れ、同じ指定境界のパラメータへ戻る射影。 -/
def comparisonResolutionProjection (X : OmegaSpectrum.{u}) {A L : OmegaSpectrum.{u}}
    (a : A ⟶ L) {U : SSet.{u}}
    (b : U ⟶ RawSpectrumMapping.relativeCornerTarget a (projection X)) :
    comparisonResolution X a b ⟶ U :=
  pullback.snd _ _

/-- 同じ解像から、境界条件を満たす元の全 Raw Hom の比較族を回収する。 -/
def comparisonResolutionFamily (X : OmegaSpectrum.{u}) {A L : OmegaSpectrum.{u}}
    (a : A ⟶ L) {U : SSet.{u}}
    (b : U ⟶ RawSpectrumMapping.relativeCornerTarget a (projection X)) :
    comparisonResolution X a b ⟶ RawSpectrumMapping.space L (middle X).toKanSequence :=
  pullback.fst _ _

/-- 比較射を含む射影の RLP は図式側でなく実 corner の RLP から証明する。 -/
lemma comparisonResolutionProjection_trivialKanFibration (X : OmegaSpectrum.{u})
    {A L : OmegaSpectrum.{u}} (a : A ⟶ L) (ha : IsSequentialRelativeCofibration a)
    {U : SSet.{u}} (b : U ⟶ RawSpectrumMapping.relativeCornerTarget a (projection X)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (comparisonResolutionProjection X a b) := by
  let := comparisonCorner_trivialKanFibration X a ha
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.pullback_snd _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem
    (p := comparisonCorner X a))⟩

/-- 同じ比較族は元の左因子上の指定族を全単体で厳密回収する。 -/
@[reassoc]
lemma comparisonResolutionFamily_left (X : OmegaSpectrum.{u}) {A L : OmegaSpectrum.{u}}
    (a : A ⟶ L) {U : SSet.{u}}
    (b : U ⟶ RawSpectrumMapping.relativeCornerTarget a (projection X)) :
    comparisonResolutionFamily X a b ≫ RawSpectrumMapping.pre a (middle X).toKanSequence =
      comparisonResolutionProjection X a b ≫ b ≫ pullback.fst _ _ := by
  dsimp only [comparisonResolutionFamily, comparisonResolutionProjection, comparisonResolution]
  have h := congrArg (· ≫ pullback.fst _ _) (pullback.condition
    (f := comparisonCorner X a) (g := b))
  simpa only [Category.assoc, comparisonCorner, RawSpectrumMapping.relativeCorner_fst] using h

/-- 同じ比較族は元の右射影への指定族も全単体で厳密回収する。 -/
@[reassoc]
lemma comparisonResolutionFamily_right (X : OmegaSpectrum.{u}) {A L : OmegaSpectrum.{u}}
    (a : A ⟶ L) {U : SSet.{u}}
    (b : U ⟶ RawSpectrumMapping.relativeCornerTarget a (projection X)) :
    comparisonResolutionFamily X a b ≫ RawSpectrumMapping.post L (projection X) =
      comparisonResolutionProjection X a b ≫ b ≫ pullback.snd _ _ := by
  dsimp only [comparisonResolutionFamily, comparisonResolutionProjection, comparisonResolution]
  have h := congrArg (· ≫ pullback.snd _ _) (pullback.condition
    (f := comparisonCorner X a) (g := b))
  simpa only [Category.assoc, comparisonCorner, RawSpectrumMapping.relativeCorner_snd] using h

/-- 固定した指定境界の比較選択空間。自由な可逆辺の空間で代用しない。 -/
def comparisonFiber (X : OmegaSpectrum.{u}) {A L : OmegaSpectrum.{u}} (a : A ⟶ L)
    (b : (RawSpectrumMapping.relativeCornerTarget a (projection X)) _⦋0⦌) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (comparisonCorner X a) b

/-- 比較射の選択 fiber は、零次も含む全境界充填を持つ。 -/
lemma comparisonFiber_isContractibleKan (X : OmegaSpectrum.{u}) {A L : OmegaSpectrum.{u}}
    (a : A ⟶ L) (ha : IsSequentialRelativeCofibration a)
    (b : (RawSpectrumMapping.relativeCornerTarget a (projection X)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (comparisonFiber X a b) := by
  let := comparisonCorner_trivialKanFibration X a ha
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan (comparisonCorner X a) b

/-- 任意の部分パラメータに既存の比較を固定したまま、同じ二境界上で延長できる。 -/
lemma exists_relative_comparisonFamily (X : OmegaSpectrum.{u}) {A L : OmegaSpectrum.{u}}
    (a : A ⟶ L) (ha : IsSequentialRelativeCofibration a) {V U : SSet.{u}}
    (j : V ⟶ U) [Mono j] (c : V ⟶ RawSpectrumMapping.space L (middle X).toKanSequence)
    (b : U ⟶ RawSpectrumMapping.relativeCornerTarget a (projection X))
    (h : c ≫ comparisonCorner X a = j ≫ b) :
    ∃ d : U ⟶ RawSpectrumMapping.space L (middle X).toKanSequence,
      j ≫ d = c ∧
      d ≫ RawSpectrumMapping.pre a (middle X).toKanSequence = b ≫ pullback.fst _ _ ∧
      d ≫ RawSpectrumMapping.post L (projection X) = b ≫ pullback.snd _ _ := by
  let := comparisonCorner_trivialKanFibration X a ha
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := comparisonCorner X a) j inferInstance
  let sq : CommSq c j (comparisonCorner X a) b := ⟨h⟩
  refine ⟨sq.lift, sq.fac_left, ?_, ?_⟩
  · have hf := congrArg (· ≫ pullback.fst _ _) sq.fac_right
    simpa only [Category.assoc, comparisonCorner, RawSpectrumMapping.relativeCorner_fst] using hf
  · have hf := congrArg (· ≫ pullback.snd _ _) sq.fac_right
    simpa only [Category.assoc, comparisonCorner, RawSpectrumMapping.relativeCorner_snd] using hf

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
