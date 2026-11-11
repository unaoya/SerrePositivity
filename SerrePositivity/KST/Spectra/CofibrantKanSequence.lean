module

public import SerrePositivity.KST.Spectra.KanSequence

/-!
概要：Kan 列の構造射を単射にする逐次的な置換。
方針：各段の比較射を suspension して元の構造射と合成し、境界の分解を適用する。
規約：このファイルでは Ω 条件の保存はまだ主張しない。
使われ方：BF 1978 §2、HTT A.3.3。cofibrant な Kan 列と段ごとの π_* 同型。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.KanSequence

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：元の列の指定段への、全ての単射に RLP を持つ比較射付きの Kan 段。
方針：段と比較射を帰納構成のデータとして束ねる。
規約：RLP は各段の構成で証明する。
使われ方：BF 1978 §2、HTT A.3.3。逐次置換の帰納。 -/
structure ReplacementStage (X : KanSequence.{u}) (n : ℕ) where
  /-- 概要：新しい Kan 段。
  方針：点つき Kan 複体を使う。
  規約：元の列と同じ宇宙。
  使われ方：BF 1978 §2。 -/
  level : PointedKanComplex.{u}
  /-- 概要：元の段への比較射。
  方針：点つき射で与える。
  規約：段 n における射。
  使われ方：BF 1978 §2。 -/
  projection : level.space ⟶ (X.level n).space
  /-- 概要：比較射の全ての単射への RLP。
  方針：境界の小対象論法から得る。
  規約：弱同値の公理を使わない。
  使われ方：BF 1978 §2、HTT A.3.3。 -/
  projection_rlp : (MorphismProperty.monomorphisms SSet.{u}).rlp projection.right

/-- 概要：置換の各段を自然数に沿って帰納的に構成する。
方針：零段は元の段、それ以降は前段の比較射を使った点つき分解の中間対象。
規約：元の各段の Kan 性によって新しい各段も Kan となる。
使われ方：BF 1978 §2、HTT A.3.3。cofibrant な列の実構成。 -/
def replacementStage (X : KanSequence.{u}) : (n : ℕ) → ReplacementStage X n
  | 0 => {
      level := X.level 0
      projection := 𝟙 _
      projection_rlp := (MorphismProperty.monomorphisms SSet.{u}).rlp.of_isIso _ }
  | n + 1 => by
      let s := replacementStage X n
      let f := PointedSimplicialSet.circle.{u} ◁ s.projection ≫ X.sigma n
      exact {
        level := ⟨PointedFactorization.middle f, inferInstance⟩
        projection := PointedFactorization.right f
        projection_rlp := PointedFactorization.right_rlp f }

/-- 概要：置換列の構造射。
方針：帰納構成で用いた境界分解の左因子を取る。
規約：各段の構造射は単射。
使われ方：BF 1978 §2。cofibrant な構造射。 -/
def replacementSigma (X : KanSequence.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (replacementStage X n).level.space ⟶ (replacementStage X (n + 1)).level.space :=
  PointedFactorization.left
    (PointedSimplicialSet.circle.{u} ◁ (replacementStage X n).projection ≫ X.sigma n)

/-- 概要：構造射が単射な Kan 列への置換。
方針：帰納構成した段と分解の左因子を束ねる。
規約：Ω 条件をこの定義には入力しない。
使われ方：BF 1978 §2、HTT A.3.3。置換後の列。 -/
def cofibrantReplacement (X : KanSequence.{u}) : KanSequence.{u} where
  level n := (replacementStage X n).level
  sigma := replacementSigma X

/-- 概要：置換から元の Kan 列への厳密な比較射。
方針：各段の右因子と分解の合成の等式を使う。
規約：構造射と厳密可換。
使われ方：BF 1978 §2、HTT A.3.3。置換の比較。 -/
def replacementProjection (X : KanSequence.{u}) : Hom X.cofibrantReplacement X where
  app n := (replacementStage X n).projection
  comm _n := (PointedFactorization.fac _).symm

/-- 概要：置換した列の全ての構造射は単射。
方針：境界分解の左因子の単射性を使う。
規約：基礎単体集合の射の単射性。
使われ方：BF 1978 §2、HTT A.3.3。cofibrant 条件。 -/
instance cofibrantReplacement_sigma_mono (X : KanSequence.{u}) (n : ℕ) :
    Mono (X.cofibrantReplacement.sigma n).right :=
  inferInstanceAs (Mono (PointedFactorization.left
    (PointedSimplicialSet.circle.{u} ◁ (replacementStage X n).projection ≫ X.sigma n)).right)

/-- 概要：置換の各段の比較射は全基点 π_* 同型。
方針：帰納構成の全ての単射への RLP と Kan な両端に既証のホモトピー逆を使う。
規約：零次数を含む。
使われ方：Goerss–Jardine I §7、BF 1978 §2。段ごとの置換の検証。 -/
theorem replacementProjection_piIsomorphism (X : KanSequence.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((replacementProjection X).app n).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight ((replacementStage X n).projection).right
    (replacementStage X n).projection_rlp

end

end SerrePositivity.KST.Spectra.KanSequence
