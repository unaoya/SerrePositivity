module
public import SerrePositivity.KST.Spectra.Limits.SpectrumBinaryProductSequence
public import SerrePositivity.KST.Spectra.Limits.SpectrumBinaryProduct

public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpectrumPoint
public import SerrePositivity.KST.Spectra.Limits.SpectrumPoint

/-!
概要：L9 の Ω スペクトルの全ての有限積と各段での計算。
方針：一点と二項積の普遍性から有限積を構成し、各段の評価が有限積を保つと示す。
規約：空の添字と任意の有限型の添字を含む。
使われ方：BF 1978 §2、HA §1.4.2、HTT 4.2.4.1 の Sp の有限積。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 概要：一点スペクトルは厳密なスペクトルの圏の終対象。
方針：各段の一点への一意な射を組み、構造射との可換性は一点への射の一意性で得る。
規約：L9 の実際の通常の圏での終対象性。
使われ方：Sp の空積と有限積の構成。 -/
def spectrumPoint_isTerminal : IsTerminal spectrumPoint.{u} :=
  IsTerminal.ofUniqueHom (fun _ ↦ {
    app _ := PointedObject.toPoint _
    comm _ := PointedObject.point_isZero.eq_of_tgt _ _ })
    (fun _ _ ↦ OmegaSpectrum.Hom.ext (fun _ ↦ PointedObject.point_isZero.eq_of_tgt _ _))

/-- 概要：スペクトルの二つの厳密射を二項積への厳密射にまとめる。
方針：Kan 列の積への射の構成を同じ各段と可換条件で束ね直す。
規約：L9 の OmegaSpectrum の射として定義する。
使われ方：二項積の通常の普遍性と有限積の構成。 -/
def spectrumBinaryProductLift {X Y Z : OmegaSpectrum.{u}} (f : Z ⟶ X) (g : Z ⟶ Y) :
    Z ⟶ spectrumBinaryProduct X Y :=
  let h := binaryProductKanSequenceLift
    (X := X.toKanSequence) (Y := Y.toKanSequence) (Z := Z.toKanSequence)
    ⟨f.app, f.comm⟩ ⟨g.app, g.comm⟩
  { app := h.app, comm := h.comm }

/-- 概要：構成した二項積と射影は通常のスペクトルの圏でも極限。
方針：段ごとの普遍射、射影則、外延性で二項錐の普遍性を確認する。
規約：持ち上げない通常の WalkingPair の二項錐を使う。
使われ方：任意の有限添字への積の拡張。 -/
def spectrumBinaryFan_isLimit (X Y : OmegaSpectrum.{u}) :
    IsLimit (BinaryFan.mk (spectrumBinaryProductFst X Y) (spectrumBinaryProductSnd X Y)) :=
  BinaryFan.isLimitMk (fun s ↦ spectrumBinaryProductLift s.fst s.snd)
    (fun s ↦ OmegaSpectrum.Hom.ext (fun n ↦ PointedObject.prodLift_fst _ _))
    (fun s ↦ OmegaSpectrum.Hom.ext (fun n ↦ PointedObject.prodLift_snd _ _))
    (fun s m hf hg ↦ OmegaSpectrum.Hom.ext (fun n ↦ by
      apply PointedObject.prod_hom_ext
      · exact (congrArg (fun k : s.pt ⟶ X ↦ k.app n) hf).trans
          (PointedObject.prodLift_fst _ _).symm
      · exact (congrArg (fun k : s.pt ⟶ Y ↦ k.app n) hg).trans
          (PointedObject.prodLift_snd _ _).symm))

/-- 概要：スペクトルの通常の圏には終対象が存在する。
方針：構成した一点スペクトルの終対象性を束ねる。
規約：このモジュール内で有限積の構成に使う。
使われ方：Mathlib の二項積と終対象からの有限積の構成。 -/
lemma spectrumHasTerminal : HasTerminal OmegaSpectrum.{u} := spectrumPoint_isTerminal.hasTerminal

/-- 概要：スペクトルの通常の圏には全ての二項積が存在する。
方針：構成した二項錐の極限性を束ねる。
規約：実際の構造射の単射性と Ω 条件は積の対象で検証済み。
使われ方：任意の有限添字への積の拡張。 -/
lemma spectrumHasBinaryProducts : HasBinaryProducts OmegaSpectrum.{u} := by
  have (X Y : OmegaSpectrum.{u}) : Limits.HasLimit (pair X Y) :=
    ⟨⟨_, spectrumBinaryFan_isLimit X Y⟩⟩
  exact hasBinaryProducts_of_hasLimit_pair _

attribute [local instance] spectrumHasTerminal spectrumHasBinaryProducts

/-- 概要：スペクトルの通常の圏には空積を含む全ての有限積が存在する。
方針：実際の終対象と二項積から Mathlib の有限帰納の構成を適用する。
規約：有限型の宇宙は任意に持ち上げられる。
使われ方：Sp の有限積の実際の錐を選ぶ。 -/
lemma spectrumHasFiniteProducts : HasFiniteProducts OmegaSpectrum.{u} :=
  hasFiniteProducts_of_has_binary_and_terminal

attribute [local instance] spectrumHasFiniteProducts

/-- 概要：各段の評価関手は終対象を保つ。
方針：一点スペクトルを評価すると点つき一点であることを使う。
規約：自然数の段を任意に固定する。
使われ方：各段の評価による有限積の保存。 -/
lemma spectrumLevel_preservesTerminal (n : ℕ) :
    PreservesLimit (Functor.empty.{0} OmegaSpectrum.{u}) (spectrumLevelFunctor n) := by
  apply preservesLimit_of_preserves_limit_cone spectrumPoint_isTerminal
  exact (isLimitMapConeEmptyConeEquiv (spectrumLevelFunctor n) spectrumPoint).symm
    PointedObject.point_isZero.isTerminal

/-- 概要：各段の評価関手は二項積を保つ。
方針：明示した二項錐を評価した錐を点つき積の標準錐と同定する。
規約：添字は通常の WalkingPair。
使われ方：各段の評価による有限積の保存。 -/
lemma spectrumLevel_preservesBinaryProducts (n : ℕ) :
    PreservesLimitsOfShape (Discrete WalkingPair) (spectrumLevelFunctor n) where
  preservesLimit {K} := by
    have : PreservesLimit (pair (K.obj ⟨.left⟩) (K.obj ⟨.right⟩)) (spectrumLevelFunctor n) := by
      apply preservesLimit_of_preserves_limit_cone (spectrumBinaryFan_isLimit _ _)
      exact (isLimitMapConeBinaryFanEquiv (spectrumLevelFunctor n) _ _).symm
        (PointedObject.prodIsLimit _ _)
    exact preservesLimit_of_iso_diagram (spectrumLevelFunctor n) (diagramIsoPair K).symm

/-- 概要：各段の評価関手は空積を含む全ての有限積を保つ。
方針：終対象と二項積の保存から有限積の保存を帰納的に得る。
規約：任意の有限添字の離散図式を扱う。
使われ方：Sp の実際の豊穣 Hom の有限積の条件。 -/
lemma spectrumLevel_preservesFiniteProducts (n : ℕ) :
    PreservesFiniteProducts (spectrumLevelFunctor n) := by
  have := spectrumLevel_preservesTerminal n
  have := preservesLimitsOfShape_pempty_of_preservesTerminal (spectrumLevelFunctor n)
  have := spectrumLevel_preservesBinaryProducts n
  exact Limits.PreservesFiniteProducts.of_preserves_binary_and_terminal _

attribute [local instance] spectrumLevel_preservesFiniteProducts

/-- 概要：有限離散図式の実際のスペクトルの積の錐。
方針：終対象と二項積から構成した有限積の通常の極限錐を選ぶ。
規約：空の添字と任意の有限型を含む。
使われ方：Sp の有限積の実際の錐の入力。 -/
def spectrumFiniteProductCone {J : Type u} [Finite J] (F : Discrete J ⥤ OmegaSpectrum.{u}) :
    Cone F := limit.cone F

/-- 概要：選んだ有限積錐は通常のスペクトルの圏の極限。
方針：構成した有限積の極限錐の普遍性を使う。
規約：有限性以外の形状条件はない。
使われ方：有限積の通常の圏での普遍性。 -/
def spectrumFiniteProductCone_isLimit {J : Type u} [Finite J]
    (F : Discrete J ⥤ OmegaSpectrum.{u}) : IsLimit (spectrumFiniteProductCone F) :=
  limit.isLimit F

/-- 概要：有限積錐は全ての段で点つき単体的集合の極限。
方針：各段の評価が有限積を保つことを通常の極限錐に適用する。
規約：空積も同じ証明で扱う。
使われ方：実際の豊穣 Hom の極限性の検証。 -/
def spectrumFiniteProductCone_level_isLimit {J : Type u} [Finite J]
    (F : Discrete J ⥤ OmegaSpectrum.{u}) (n : ℕ) :
    IsLimit (spectrumLevelCone (spectrumFiniteProductCone F) n) :=
  isLimitOfPreserves (spectrumLevelFunctor n) (spectrumFiniteProductCone_isLimit F)

local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance (X Y : OmegaSpectrum.{u}) : KanComplex (SimplicialCategory.sHom X Y) :=
  OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 概要：有限積錐は全ての実際の豊穣 Hom で極限となる。
方針：各段の極限性を写像空間の族の普遍性へ渡す。
規約：L9 の塔の極限で定義された写像空間を使う。
使われ方：HTT 4.2.4.1 の有限離散図式の Hom 条件。 -/
def spectrumFiniteProductCone_hom_isLimit {J : Type u} [Finite J]
    (F : Discrete J ⥤ OmegaSpectrum.{u}) (X : OmegaSpectrum.{u}) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone (spectrumFiniteProductCone F) X) :=
  spectrumHomCone_isLimit_of_levelwise _ (spectrumFiniteProductCone_level_isLimit F) X

/-- 概要：有限離散図式の積の錐を L9 の Sp の錐へ送る。
方針：実際の厳密な有限積錐に coherent nerve の錐の構成を適用する。
規約：底は有限離散図式の nerve、空の添字も許す。
使われ方：HTT 4.2.4.1、Sp の有限積の公開。 -/
def spectrumFiniteProductInfinityCone {J : Type u} [Finite J]
    (F : Discrete J ⥤ OmegaSpectrum.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (spectrumFiniteProductCone F)

/-- 概要：スペクトルの有限積錐は Sp の実際の極限錐。
方針：全ての実際の豊穣 Hom の極限性を離散図式の比較定理へ渡す。
規約：空積を含み、有限性以外の追加仮定は置かない。
使われ方：HTT 4.2.4.1 の双対、HA §1.4.2、γ3c の Sp の全ての有限積。 -/
lemma spectrumFiniteProductInfinityCone_isLimit {J : Type u} [Finite J]
    (F : Discrete J ⥤ OmegaSpectrum.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (spectrumFiniteProductInfinityCone F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_discrete_homLimit _ (spectrumFiniteProductCone_hom_isLimit F)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
