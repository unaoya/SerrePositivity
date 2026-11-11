module
public import SerrePositivity.KST.Spectra.Limits.SpectrumBinaryProductSequence

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SmashProductMono
public import SerrePositivity.KST.Spectra.Limits.SpectrumHomLimitFamilies

/-!
概要：L9 の Ω スペクトルの段ごとの二項積。
方針：smash と積の比較の単射性と Kan Ω 列の積の Ω 条件を組み合わせる。
規約：L9 の実際の単射な構造射を持つ OmegaSpectrum を構成する。
使われ方：BF 1978 §2、HA §1.4.2、HTT 4.2.4.1 の Sp の二項積。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 概要：積の懸垂構造射は smash と積の比較に二構造射の積を続けたもの。
方針：二つの射影と積の普遍性で等式を確認する。
規約：点つき射の厳密な等式。
使われ方：構造射の単射性を比較射と二構造射へ分解する。 -/
lemma binaryProductSigma_factor {A B A' B' : PointedSimplicialSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A ⟶ A') (t : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension B ⟶ B') :
    binaryProductSigma s t =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashProductComparison PointedSimplicialSet.circle.{u} A B ≫ PointedObject.prodMap s t := by
  apply PointedObject.prod_hom_ext <;>
    simp [binaryProductSigma, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashProductComparison, PointedObject.prodMap, Category.assoc] <;> rfl

/-- 概要：単射な二つの構造射から作る積の懸垂構造射も単射。
方針：smash と二項積の単射な比較と二つの単射の積を合成する。
規約：二構造射の基礎単体写像のモノ射性だけを要求する。
使われ方：L9 の OmegaSpectrum の sigma_mono 条件の検証。 -/
instance binaryProductSigma_mono {A B A' B' : PointedSimplicialSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A ⟶ A') (t : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension B ⟶ B') [Mono s.right] [Mono t.right] :
    Mono (binaryProductSigma s t).right := by
  rw [binaryProductSigma_factor, Under.comp_right, PointedObject.prodMap_right]
  have : Mono (s.right ⊗ₘ t.right) := ⟨by
    intro Z f g h
    apply CartesianMonoidalCategory.hom_ext
    · apply (cancel_mono s.right).mp
      have h' := congrArg (fun k ↦ k ≫ CartesianMonoidalCategory.fst A'.right B'.right) h
      simpa only [Category.assoc, CartesianMonoidalCategory.tensorHom_fst] using h'
    · apply (cancel_mono t.right).mp
      have h' := congrArg (fun k ↦ k ≫ CartesianMonoidalCategory.snd A'.right B'.right) h
      simpa only [Category.assoc, CartesianMonoidalCategory.tensorHom_snd] using h'⟩
  infer_instance

/-- 概要：L9 の二つの Ω スペクトルの段ごとの二項積。
方針：Kan 列の積を単射な構造射と全基点の Ω 条件によって束ねる。
規約：段は点つき通常積で、構造射は binaryProductSigma。
使われ方：BF 1978 §2、Sp の二項積の実際の頂点。 -/
def spectrumBinaryProduct (X Y : OmegaSpectrum.{u}) : OmegaSpectrum.{u} :=
  (binaryProductKanSequence X.toKanSequence Y.toKanSequence).toOmegaSpectrum
    (fun n ↦ binaryProductSigma_mono (X.sigma n) (Y.sigma n))
    (binaryProductKanSequence_omega X.toKanSequence Y.toKanSequence
      X.toKanSequence_omega Y.toKanSequence_omega)

/-- 概要：Ω スペクトルの二項積から第一の因子への射影。
方針：Kan 列の積の射影の各段と可換条件を使う。
規約：L9 の実際の厳密なスペクトル射。
使われ方：Sp の二項積の錐の第一の脚。 -/
def spectrumBinaryProductFst (X Y : OmegaSpectrum.{u}) : spectrumBinaryProduct X Y ⟶ X where
  app := (binaryProductKanSequenceFst X.toKanSequence Y.toKanSequence).app
  comm := (binaryProductKanSequenceFst X.toKanSequence Y.toKanSequence).comm

/-- 概要：Ω スペクトルの二項積から第二の因子への射影。
方針：Kan 列の積の射影の各段と可換条件を使う。
規約：L9 の実際の厳密なスペクトル射。
使われ方：Sp の二項積の錐の第二の脚。 -/
def spectrumBinaryProductSnd (X Y : OmegaSpectrum.{u}) : spectrumBinaryProduct X Y ⟶ Y where
  app := (binaryProductKanSequenceSnd X.toKanSequence Y.toKanSequence).app
  comm := (binaryProductKanSequenceSnd X.toKanSequence Y.toKanSequence).comm

/-- 概要：指定した二つのスペクトルからなる離散図式。
方針：二対象の添字を Hom の宇宙まで持ち上げて離散関手にする。
規約：添字は Discrete (ULift WalkingPair)。
使われ方：HTT 4.2.4.1 の離散図式への共有界面へ二項積を渡す。 -/
def spectrumBinaryProductDiagram (X Y : OmegaSpectrum.{u}) :
    Discrete (ULift.{u} WalkingPair) ⥤ OmegaSpectrum.{u} :=
  Discrete.functor fun i ↦ match i.down with
    | .left => X
    | .right => Y

/-- 概要：二つのスペクトルの段ごとの積と射影からなる厳密な錐。
方針：添字の二つの場合に射影を与える。
規約：通常の圏の錐を先に構成する。
使われ方：Sp の coherent nerve の二項積錐の入力。 -/
def spectrumBinaryProductCone (X Y : OmegaSpectrum.{u}) :
    Cone (spectrumBinaryProductDiagram X Y) where
  pt := spectrumBinaryProduct X Y
  π := Discrete.natTrans (by
    rintro ⟨⟨i⟩⟩
    cases i
    · exact spectrumBinaryProductFst X Y
    · exact spectrumBinaryProductSnd X Y)

/-- 概要：スペクトルの二項積錐の各段は点つき単体的集合の実際の極限。
方針：二つの脚を組にする射を与え、射影則と外延性で普遍性を検証する。
規約：全ての自然数段を扱う。
使われ方：Sp の実際の豊穣 Hom の極限の検証。 -/
def spectrumBinaryProductCone_level_isLimit (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    IsLimit (spectrumLevelCone (spectrumBinaryProductCone X Y) n) where
  lift s := PointedObject.prodLift (s.π.app (.mk ⟨.left⟩)) (s.π.app (.mk ⟨.right⟩))
  fac s i := by
    rcases i with ⟨⟨i⟩⟩
    cases i
    · exact PointedObject.prodLift_fst _ _
    · exact PointedObject.prodLift_snd _ _
  uniq s m hm := by
    apply PointedObject.prod_hom_ext
    · exact (hm (.mk ⟨.left⟩)).trans (PointedObject.prodLift_fst _ _).symm
    · exact (hm (.mk ⟨.right⟩)).trans (PointedObject.prodLift_snd _ _).symm

local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance (X Y : OmegaSpectrum.{u}) : KanComplex (SimplicialCategory.sHom X Y) :=
  OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 概要：スペクトルの二項積錐は全ての実際の豊穣 Hom で極限となる。
方針：段ごとの点つき極限を写像空間の族の普遍性へ渡す。
規約：L9 の塔の極限による写像空間を使う。
使われ方：HTT 4.2.4.1 の Sp の二項積の Hom 条件。 -/
def spectrumBinaryProductCone_hom_isLimit (X Y Z : OmegaSpectrum.{u}) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone (spectrumBinaryProductCone X Y) Z) :=
  spectrumHomCone_isLimit_of_levelwise (spectrumBinaryProductCone X Y)
    (spectrumBinaryProductCone_level_isLimit X Y) Z

/-- 概要：段ごとの二項積錐から L9 の Sp の実際の錐を作る。
方針：厳密な錐を coherent nerve へ送る。
規約：底は持ち上げた二対象の離散図式の nerve。
使われ方：BF 1978 §2、HTT 4.2.4.1 の Sp の二項積。 -/
def spectrumBinaryProductInfinityCone (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (spectrumBinaryProductDiagram X Y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (spectrumBinaryProductCone X Y)

/-- 概要：L9 の二つの Ω スペクトルの段ごとの積は Sp の二項積となる。
方針：全ての豊穣 Hom の極限性と離散図式の比較定理から極限錐性を得る。
規約：構造射の単射性と全基点の Ω 条件は構成時に検証済みで追加仮定はない。
使われ方：HTT 4.2.4.1 の双対、HA §1.4.2、γ3c の Sp の二項積の公開結果。 -/
lemma spectrumBinaryProductInfinityCone_isLimit (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (spectrumBinaryProductInfinityCone X Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_discrete_homLimit (spectrumBinaryProductCone X Y)
    (spectrumBinaryProductCone_hom_isLimit X Y)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
