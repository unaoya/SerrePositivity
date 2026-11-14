module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.Cofinality
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms
public import Mathlib.CategoryTheory.SmallObject.Basic

/-!
概要：任意の射の right anodyne な単射と right fibration への因子分解。
方針：有限表示可能な right ホーンに可算小対象論法を適用する。
規約：モデル構造の弱同値や straightening は使わない。
使われ方：Kerodon §4.2.4（Tag 014S） の双対、Quillen A の因子分解による還元。

対応節は Kerodon 4.2（Tag 014H）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

/-- 概要：right ホーンを小さい型で添字づけた射の族。
方針：次数と欠ける面の対を用いる。
規約：正次元のホーンのみ。
使われ方：小対象論法の添字型。 -/
def cofinalRightHornFamily : MorphismProperty SSet.{u} :=
  .ofHoms (fun s : Σ n : ℕ, {i : Fin (n + 2) // 0 < i} ↦
    (horn (s.1 + 1) s.2.val).ι)

/-- 概要：小さい族は既存の right ホーン包含の性質と一致する。
方針：両方の構成子を同じ次数と面の添字で往復する。
規約：射の等式による移送ではなく性質全体の等式。
使われ方：因子分解を既存の anodyne と fibration へ接続する。 -/
lemma cofinalRightHornFamily_eq : cofinalRightHornFamily.{u} = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions := by
  ext X Y f
  constructor
  · rintro ⟨⟨n, i, hi⟩⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions.intro i hi
  · rintro ⟨i, hi⟩
    change MorphismProperty.ofHoms
      (fun s : Σ n : ℕ, {i : Fin (n + 2) // 0 < i} ↦
        (horn (s.1 + 1) s.2.val).ι) _
    exact ⟨(⟨_, ⟨i, hi⟩⟩ : Σ n : ℕ, {i : Fin (n + 2) // 0 < i})⟩

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

/-- 概要：right ホーンの族は小対象論法の意味で小さい。
方針：小さい型で添字づけた射の族の一般補題を使う。
規約：単体集合と同じ宇宙で小ささを測る。
使われ方：可算小対象論法。 -/
instance cofinalRightHornFamily_isSmall : MorphismProperty.IsSmall.{u} cofinalRightHornFamily.{u} :=
  isSmall_ofHoms ..

/-- 概要：right ホーンは可算小対象論法の基数条件を満たす。
方針：各ホーンの有限表示可能性を使う。
規約：小対象論法の反復基数は aleph0。
使われ方：関手的な因子分解の存在。 -/
instance cofinalRightHornFamily_isCardinalForSmallObjectArgument :
    IsCardinalForSmallObjectArgument cofinalRightHornFamily.{u} Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      obtain ⟨⟨n, j, hj⟩⟩ := hi
      infer_instance
    infer_instance

/-- 概要：right ホーンの族に小対象論法を適用できる。
方針：可算の基数条件を束ねる。
規約：充填性を元の射に要求しない。
使われ方：cofinality の還元用の因子分解。 -/
instance cofinalRightHornFamily_hasSmallObjectArgument :
    HasSmallObjectArgument.{u} cofinalRightHornFamily.{u} :=
  ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

/-- 概要：right ホーンの左セル閉包の射は単射。
方針：単射の余積・押し出し・超限合成・retract による閉性を使う。
規約：右持ち上げ性に対する左持ち上げ性として閉包を取る。
使われ方：因子分解の左因子の単射性。 -/
lemma cofinalRightHornFamily_llp_rlp_le_monomorphisms :
    cofinalRightHornFamily.{u}.rlp.llp ≤ monomorphisms SSet := by
  rw [llp_rlp_of_hasSmallObjectArgument]
  rw [retracts_le_iff, transfiniteCompositions_le_iff, pushouts_le_iff, coproducts_le_iff]
  rintro X Y f ⟨⟨n, i, hi⟩⟩
  exact monomorphisms.infer_property _

/-- 概要：任意の射を right anodyne な単射と right fibration の合成に分解できる。
方針：小対象論法で得た因子を既存のホーンの性質に同定する。
規約：合成の一致は厳密な等式。
使われ方：Kerodon §4.2.4（Tag 014S） の双対、Quillen A の還元。 -/
lemma exists_rightAnodyne_rightFibration_factorization {X Y : SSet.{u}} (f : X ⟶ Y) :
    ∃ (Z : SSet.{u}) (i : X ⟶ Z) (p : Z ⟶ Y),
      Mono i ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions i ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p ∧ i ≫ p = f := by
  let d := factorizationData cofinalRightHornFamily.rlp.llp cofinalRightHornFamily.rlp f
  refine ⟨d.Z, d.i, d.p, cofinalRightHornFamily_llp_rlp_le_monomorphisms _ d.hi, ?_, ?_, d.fac⟩
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions.rlp.llp d.i
    simpa only [cofinalRightHornFamily_eq] using d.hi
  · constructor
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions.rlp d.p
    simpa only [cofinalRightHornFamily_eq] using d.hp

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.0.0.6"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.exists_rightAnodyne_rightFibration_factorization
