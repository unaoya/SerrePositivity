module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningMappingComparison
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulEquivalence
public import SerrePositivity.InfinityCategories.Core.EquivalenceFullyFaithful

/-!
概要：実際の straightening の同値性を、その実際の写像空間作用の同値性へ還元する。
方針：全頂点を元の left fibrations で表し、既証明の本質的全射性と F0 の判定を使う。
規約：独立な比較同値の存在を充満忠実性と取り違えず、単位・余単位を仮定しない。
使われ方：残る全高次の比較の照合から分類同値を直接結論する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 実際の分類写像の充満忠実性は、端点表示を揃えた元の全写像空間作用で判定できる。 -/
lemma leftStraighteningInfinityMap_isFullyFaithful_iff (B : SSet.{u}) :
    IsFullyFaithful (leftStraighteningInfinityMap B) ↔
      ∀ p q : LeftFibrationObject B,
        IsQCatEquivalence (leftStraighteningInfinityPinchedHomMap p.val.hom q.val.hom) := by
  constructor
  · intro h p q
    apply (leftStraighteningInfinityPinchedHomMap_isQCatEquivalence_iff
      p.val.hom q.val.hom).mpr
    exact (h (leftFibrationInfinityVertex p.val.hom)
      (leftFibrationInfinityVertex q.val.hom)).isQCatEquivalence
  · intro h x y
    obtain ⟨p, rfl⟩ := (coherentNerveVertexEquiv (LeftFibrationObject B)).surjective x
    obtain ⟨q, rfl⟩ := (coherentNerveVertexEquiv (LeftFibrationObject B)).surjective y
    exact ((leftStraighteningInfinityPinchedHomMap_isQCatEquivalence_iff
      p.val.hom q.val.hom).mp (h p q)).isSimplicialHomotopyEquivalence

/-- 実際の分類写像の写像空間作用が同値なら、既存の本質的全射性で分類同値が閉じる。 -/
lemma leftStraighteningInfinityMap_isQCatEquivalence_of_pinchedHomMap
    (B : SSet.{u})
    (h : ∀ p q : LeftFibrationObject B,
      IsQCatEquivalence (leftStraighteningInfinityPinchedHomMap p.val.hom q.val.hom)) :
    IsQCatEquivalence (leftStraighteningInfinityMap B) :=
  isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    ((leftStraighteningInfinityMap_isFullyFaithful_iff B).mpr h)
    (leftStraighteningInfinityMap_isEssentiallySurjective B)

/-- 分類写像の同値性の残る必要十分条件は、同じ写像の全 Hom 上の同値性。 -/
lemma leftStraighteningInfinityMap_isQCatEquivalence_iff_pinchedHomMap (B : SSet.{u}) :
    IsQCatEquivalence (leftStraighteningInfinityMap B) ↔
      ∀ p q : LeftFibrationObject B,
        IsQCatEquivalence (leftStraighteningInfinityPinchedHomMap p.val.hom q.val.hom) :=
  ⟨fun h => (leftStraighteningInfinityMap_isFullyFaithful_iff B).mp h.isFullyFaithful,
    leftStraighteningInfinityMap_isQCatEquivalence_of_pinchedHomMap B⟩

end SerrePositivity.InfinityCategories
