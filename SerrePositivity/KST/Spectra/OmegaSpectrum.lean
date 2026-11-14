module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.Spectra.SuspensionLoop
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.HomotopyIsomorphism
public import SerrePositivity.KST.Spectra.TruncatedMapping

/-!
概要：BF の cofibrant–fibrant な Ω スペクトルの対象と写像空間。
方針：構造射を単射とし、随伴構造射の全基点の π_* 同型を要求する。
規約：厳密 Ω 同型は要求しない。coherent nerve と整数次数の群は後続の工程。
使われ方：Bousfield–Friedlander 1978 §2、HTT A.3.3、HA §1.4.2。
-/

@[expose] public section

universe u

open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra

/-- 概要：基点と Kan 性を持つ単体集合。
方針：基礎の点つき単体集合と Kan 性の証明を束ねる。
規約：Kan 性は既存のホーン充填条件。
使われ方：BF 1978 §2。スペクトルの各段。 -/
structure PointedKanComplex where
  /-- 概要：各段の点つき単体集合。
  方針：Under の基礎定義を使う。
  規約：宇宙 u。
  使われ方：BF 1978 §2。 -/
  space : PointedSimplicialSet.{u}
  /-- 概要：各段のホーン充填性。
  方針：Mathlib の KanComplex の証明を保持する。
  規約：追加公理ではなく対象の条件。
  使われ方：BF 1978 §2。 -/
  kan : KanComplex space.right

attribute [instance] PointedKanComplex.kan

/-- 概要：単射構造と π_* 同型の Ω 条件を持つスペクトル。
方針：点つき Kan 複体の列と suspension の構造射を束ねる。
規約：BF の cofibrant–fibrant な対象のモデル。導来写像空間との比較は γ3 後。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。Sp の対象。 -/
structure OmegaSpectrum where
  /-- 概要：自然数で添字づけた点つき Kan 複体。
  方針：Kan 性を各段で束ねる。
  規約：零段から始める。
  使われ方：BF 1978 §2。 -/
  level : ℕ → PointedKanComplex.{u}
  /-- 概要：suspension から次段への構造射。
  方針：通常の点つき単体集合の射を使う。
  規約：厳密同型は要求しない。
  使われ方：BF 1978 §2、HA §1.4.2。 -/
  sigma : ∀ n, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (level n).space ⟶ (level (n + 1)).space
  /-- 概要：構造射の単射性。
  方針：基礎単体集合の Mono を保持する。
  規約：cell 分解と同値な cofibrant 条件。
  使われ方：BF 1978 §2。Hom の塔の相対充填。 -/
  sigma_mono : ∀ n, Mono (sigma n).right
  /-- 概要：随伴構造射は全基点で π_* 同型。
  方針：実装済みのホモトピー類への誘導写像の全単射性で表す。
  規約：零次数を含む。厳密 Ω 同型は要求しない。
  使われ方：BF 1978 §2、HA §1.4.2。段によらない安定ホモトピー群。 -/
  omega_condition : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
    ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (level n).space (level (n + 1)).space) (sigma n)).right

attribute [instance] OmegaSpectrum.sigma_mono

namespace OmegaSpectrum

noncomputable section

/-- 概要：スペクトルの構造射が定める境界比較。
方針：写像を suspension し、標的の構造射と合成する。
規約：単体集合の全次数で自然な射。
使われ方：BF 1978 §2、HTT A.3.3。切断 Hom の引き戻し。 -/
def mappingStep (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    (PointedObject.basedHom (X.level n).space (Y.level n).space).right ⟶
      (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 1)).space).right :=
  (suspensionHom (X.level n).space (Y.level n).space).right ≫
    (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.sigma n)).right

/-- 概要：n 段までのスペクトルの切断写像空間。
方針：構造射による制限と境界比較を引き戻す塔を用いる。
規約：Ω 条件はこの構成には不要。
使われ方：BF 1978 §2、HTT A.3.3。Hom の塔。 -/
abbrev truncatedHom (X Y : OmegaSpectrum.{u}) (n : ℕ) : SSet.{u} :=
  TruncatedMapping.space (fun n ↦ (X.level n).space) (fun n ↦ (Y.level n).space)
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) X.sigma (mappingStep X Y) n

/-- 概要：スペクトルの写像空間として用いる全切断の整合族。
方針：構造射と可換する写像の切断の逆極限を取る。
規約：厳密な射・合成との同定は後続補題で検査する。
使われ方：BF 1978 §2、HTT A.3.3。coherent nerve の Hom の候補。 -/
abbrev mappingSpace (X Y : OmegaSpectrum.{u}) : SSet.{u} :=
  TruncatedMapping.total (fun n ↦ (X.level n).space) (fun n ↦ (Y.level n).space)
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) X.sigma (mappingStep X Y)

/-- 概要：スペクトルの整合写像空間は Kan 複体。
方針：構造射の単射性と各段の Kan 性を塔の構成に適用する。
規約：Ω 条件を使わない。射・合成との同定は別途行う。
使われ方：BF 1978 §2、HTT A.3.3。γ1 の局所 Kan 性への構成部品。 -/
instance mappingSpace_kanComplex (X Y : OmegaSpectrum.{u}) : KanComplex (mappingSpace X Y) :=
  TruncatedMapping.total_kanComplex _ _ _ _ _

end

end OmegaSpectrum

end SerrePositivity.KST.Spectra

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.4.2.8" (partial := special) "仮定：標的は点付き Kan 空間（Lean が強い：有限極限を持つ一般の C ではない）。結論：Ω スペクトルとその coherent nerve（Lean が弱い：有限点付き空間からの縮約切除関手の充満部分圏との比較がない）。"] _root_.SerrePositivity.KST.Spectra.OmegaSpectrum
