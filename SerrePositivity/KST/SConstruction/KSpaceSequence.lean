module
public import SerrePositivity.KST.SConstruction.KanAssemblySequence
public import SerrePositivity.KST.SConstruction.BoundaryKComparison

/-! # K 空間を零段とする反復 S の Kan 列
概要：零段を Ω|ιS•C| とし、正の段を反復 S の Kan 実現とする列を構成する。
方針：零段の構造射は随伴の余単位、正の段は境界商の列の構造射を使う。
規約：Ω 条件は KOmegaSpectrum、連結性は MultiStageConnected で証明する。
使われ方：連結 K スペクトルの元の列。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet

/-- 概要：K 空間を零段とする反復 S の各 Kan 段。
方針：零段は既定の境界商の K 空間、後続段は全零境界商の Kan 実現を取る。
規約：第 r+1 段は r+1 重 S。使われ方：同じ列の全段の座標。 -/
def kKanSequenceLevel (X : StableModel.{u}) : ℕ → Spectra.PointedKanComplex.{u}
  | 0 => ⟨boundaryKSpaceFunctor.obj X, inferInstance⟩
  | r + 1 => (boundaryKanSequence X).level r

/-- 概要：K 空間を零段とする列の suspension 構造射。
方針：零段は loop の恒等射を uncurry し、後続では反復 S の構造射を使う。
規約：零段での随伴射は恒等射。使われ方：K 空間と実現の接続。 -/
def kKanSequenceSigma (X : StableModel.{u}) :
    ∀ r, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (kKanSequenceLevel X r).space ⟶
      (kKanSequenceLevel X (r + 1)).space
  | 0 => (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _).symm (𝟙 (boundaryKSpaceFunctor.obj X))
  | r + 1 => (boundaryKanSequence X).sigma r

/-- 概要：零段が定義済みの K 空間である実際の Kan 列。
方針：構成した各段と suspension 構造射を束ねる。
規約：Ω 条件や連結性を入力にしない。使われ方：単射構造射の置換の入力。 -/
def kKanSequence (X : StableModel.{u}) : Spectra.KanSequence.{u} where
  level := kKanSequenceLevel X
  sigma := kKanSequenceSigma X

/-- 概要：零段の随伴構造射は K 空間の恒等射。
方針：随伴同値の逆方向の消去。
規約：厳密等号。使われ方：零段の Ω 条件の確認。 -/
lemma kKanSequence_zero_adjoint (X : StableModel.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _) ((kKanSequence X).sigma 0) =
      𝟙 (boundaryKSpaceFunctor.obj X) := Equiv.apply_symm_apply _ _

/-- 概要：K の候補列の零段の随伴構造射は全基点 π 同型。
方針：零段の随伴構造射を恒等射へ書き直す。
規約：正の段については主張しない。使われ方：Ω 条件の零段。 -/
lemma kKanSequence_zero_piIsomorphism (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _) ((kKanSequence X).sigma 0)).right := by
  rw [kKanSequence_zero_adjoint]
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.id _

/-- 概要：K の候補列の単射構造射を持つ Kan 置換列。
方針：L9 の Kan 列の逐次置換を適用する。
規約：Ω 条件はまだ主張しない。使われ方：BF の構造射の単射条件。 -/
def monicKKanSequence (X : StableModel.{u}) : Spectra.KanSequence.{u} :=
  (kKanSequence X).cofibrantReplacement

/-- 概要：K の置換列の全構造射は単射。
方針：L9 の単射置換の性質。
規約：底の単体集合の射について。使われ方：BF の構造射条件。 -/
instance monicKKanSequence_sigma_mono (X : StableModel.{u}) (r : ℕ) :
    Mono ((monicKKanSequence X).sigma r).right :=
  Spectra.KanSequence.cofibrantReplacement_sigma_mono _ r

/-- 概要：単射構造射の K の候補列から元の列への厳密な比較。
方針：L9 の置換射影。
規約：全段の構造射と厳密可換。使われ方：構成した反復 S の列との比較。 -/
def monicKKanSequenceProjection (X : StableModel.{u}) :
    Spectra.KanSequence.Hom (monicKKanSequence X) (kKanSequence X) :=
  Spectra.KanSequence.replacementProjection _

/-- 概要：K の候補列の置換の比較射は各段で全基点 π 同型。
方針：L9 の Kan 列の射影の比較定理を使う。
規約：零次数も含む。使われ方：BF の単射模型と元の反復 S の比較。 -/
lemma monicKKanSequenceProjection_piIsomorphism (X : StableModel.{u}) (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((monicKKanSequenceProjection X).app r).right :=
  Spectra.KanSequence.replacementProjection_piIsomorphism _ r

/-- 概要：単射構造射の候補列の零段は定義済みの K 空間と一致する。
方針：L9 の置換は零段を保つ。
規約：厳密等号。使われ方：K 空間とスペクトル候補の座標の照合。 -/
lemma monicKKanSequence_zero (X : StableModel.{u}) :
    ((monicKKanSequence X).level 0).space = boundaryKSpaceFunctor.obj X := rfl

end SerrePositivity.KST.SConstruction
