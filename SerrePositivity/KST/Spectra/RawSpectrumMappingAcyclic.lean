module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingFamily
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.MonoRightHomotopyEquivalence
public import SerrePositivity.KST.Spectra.MappingOmegaSequence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence

/-!
概要：一般の Kan 列への整合写像空間で、段ごとの全単射 RLP は後合成で保存される。
方針：相対的な段の持ち上げを整合族へまとめ、元の評価に沿う厳密な因子分解を証明する。
規約：BF 源の単射構造だけを用いる。使われ方：BF cotensor の置換射影の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 段ごとに全単射 RLP を持つ Kan 列の射は全写像空間でも全単射 RLP を持つ。 -/
lemma post_rlp (X : OmegaSpectrum.{u}) {Y Z : KanSequence.{u}} (p : KanSequence.Hom Y Z)
    (hp : ∀ n, (MorphismProperty.monomorphisms SSet.{u}).rlp (p.app n).right) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (post X p) := by
  intro T U j hj
  let : Mono j := hj
  constructor
  intro a b sq
  obtain ⟨f, ha, hb, hf⟩ := monoFamily X p hp j a b sq.w
  let l := lift X Y f hf
  have hl (n : ℕ) : l ≫ evaluation X Y n = f n := lift_evaluation _ _ _ _ n
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply hom_ext X Y
    intro n
    rw [Category.assoc, hl]
    exact ha n
  · apply hom_ext X Z
    intro n
    rw [Category.assoc, post_evaluation X p n, ← Category.assoc, hl]
    exact hb n

/-- 同じ後合成は、実際の trivial Kan fibration である。 -/
lemma post_trivialKanFibration (X : OmegaSpectrum.{u}) {Y Z : KanSequence.{u}}
    (p : KanSequence.Hom Y Z)
    (hp : ∀ n, (MorphismProperty.monomorphisms SSet.{u}).rlp (p.app n).right) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (post X p) := ⟨post_rlp X p hp⟩

/-- 全単射 RLP を持つ後合成は全基点で π 同型。 -/
lemma post_piIsomorphism (X : OmegaSpectrum.{u}) {Y Z : KanSequence.{u}}
    (p : KanSequence.Hom Y Z)
    (hp : ∀ n, (MorphismProperty.monomorphisms SSet.{u}).rlp (p.app n).right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (post X p) := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (post_rlp X p hp)

/-- BF cotensor の射影は実際の写像空間でも全単射 RLP を持つ。 -/
lemma cotensorProjection_rlp (X Y : OmegaSpectrum.{u}) (A : PointedSimplicialSet.{u}) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (post X (OmegaSpectrum.cotensorProjection A Y)) :=
  post_rlp X _ (fun n ↦
    (KanSequence.replacementStage (KanSequence.mapping A Y.toKanSequence) n).projection_rlp)

/-- BF cotensor の写像空間と、置換前の内部 Hom 列への写像空間の実際の比較は π 同型。 -/
lemma cotensorProjection_piIsomorphism (X Y : OmegaSpectrum.{u})
    (A : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (post X (OmegaSpectrum.cotensorProjection A Y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (cotensorProjection_rlp X Y A)

/-- 元の BF cotensor の豊穣 Hom と置換前の写像空間の実際の同値。 -/
def cotensorProjectionEquivalence (X Y : OmegaSpectrum.{u}) (A : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (OmegaSpectrum.mappingSpace X (OmegaSpectrum.cotensor A Y))
      (space X (KanSequence.mapping A Y.toKanSequence)) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (post X (OmegaSpectrum.cotensorProjection A Y)) :=
    ⟨cotensorProjection_rlp X Y A⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (post X (OmegaSpectrum.cotensorProjection A Y))

/-- 構成した同値の順写像は、元の置換射影による後合成。 -/
lemma cotensorProjectionEquivalence_hom (X Y : OmegaSpectrum.{u})
    (A : PointedSimplicialSet.{u}) :
    (cotensorProjectionEquivalence X Y A).hom =
      post X (OmegaSpectrum.cotensorProjection A Y) := rfl

end SerrePositivity.KST.Spectra.RawSpectrumMapping
