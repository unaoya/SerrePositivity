module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.Cofinality
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms
public import Mathlib.CategoryTheory.SmallObject.Basic

/-!
概要：任意の射の left anodyne な単射と left fibration への因子分解。
方針：有限表示可能な left ホーンに可算小対象論法を適用する。
規約：モデル構造の弱同値や straightening は使わない。
使われ方：Kerodon §4.2.4（Tag 014S）、Quillen A の因子分解による還元。

対応節は Kerodon 4.2（Tag 014H）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

/-- 概要：left ホーンを小さい型で添字づけた射の族。
方針：次数と欠ける面の対を用いる。
規約：正次元のホーンのみ。
使われ方：小対象論法の添字型。 -/
def cofinalLeftHornFamily : MorphismProperty SSet.{u} :=
  .ofHoms (fun s : Σ n : ℕ, {i : Fin (n + 2) // i < Fin.last (n + 1)} ↦
    (horn (s.1 + 1) s.2.val).ι)

/-- 概要：小さい族は既存の left ホーン包含の性質と一致する。
方針：両方の構成子を同じ次数と面の添字で往復する。
規約：射の等式による移送ではなく性質全体の等式。
使われ方：因子分解を既存の anodyne と fibration へ接続する。 -/
lemma cofinalLeftHornFamily_eq : cofinalLeftHornFamily.{u} = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions := by
  ext X Y f
  constructor
  · rintro ⟨⟨n, i, hi⟩⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions.intro i hi
  · rintro ⟨i, hi⟩
    change MorphismProperty.ofHoms
      (fun s : Σ n : ℕ, {i : Fin (n + 2) // i < Fin.last (n + 1)} ↦
        (horn (s.1 + 1) s.2.val).ι) _
    exact ⟨(⟨_, ⟨i, hi⟩⟩ : Σ n : ℕ, {i : Fin (n + 2) // i < Fin.last (n + 1)})⟩

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

/-- 概要：left ホーンの族は小対象論法の意味で小さい。
方針：小さい型で添字づけた射の族の一般補題を使う。
規約：単体集合と同じ宇宙で小ささを測る。
使われ方：可算小対象論法。 -/
instance cofinalLeftHornFamily_isSmall : MorphismProperty.IsSmall.{u} cofinalLeftHornFamily.{u} :=
  isSmall_ofHoms ..

/-- 概要：left ホーンは可算小対象論法の基数条件を満たす。
方針：各ホーンの有限表示可能性を使う。
規約：小対象論法の反復基数は aleph0。
使われ方：関手的な因子分解の存在。 -/
instance cofinalLeftHornFamily_isCardinalForSmallObjectArgument :
    IsCardinalForSmallObjectArgument cofinalLeftHornFamily.{u} Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      obtain ⟨⟨n, j, hj⟩⟩ := hi
      infer_instance
    infer_instance

/-- 概要：left ホーンの族に小対象論法を適用できる。
方針：可算の基数条件を束ねる。
規約：充填性を元の射に要求しない。
使われ方：cofinality の還元用の因子分解。 -/
instance cofinalLeftHornFamily_hasSmallObjectArgument :
    HasSmallObjectArgument.{u} cofinalLeftHornFamily.{u} :=
  ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

/-- 概要：left ホーンの左セル閉包の射は単射。
方針：単射の余積・押し出し・超限合成・retract による閉性を使う。
規約：右持ち上げ性に対する左持ち上げ性として閉包を取る。
使われ方：因子分解の左因子の単射性。 -/
lemma cofinalLeftHornFamily_llp_rlp_le_monomorphisms :
    cofinalLeftHornFamily.{u}.rlp.llp ≤ monomorphisms SSet := by
  rw [llp_rlp_of_hasSmallObjectArgument]
  rw [retracts_le_iff, transfiniteCompositions_le_iff, pushouts_le_iff, coproducts_le_iff]
  rintro X Y f ⟨⟨n, i, hi⟩⟩
  exact monomorphisms.infer_property _

/-- 概要：任意の射を left anodyne な単射と left fibration の合成に分解できる。
方針：小対象論法で得た因子を既存のホーンの性質に同定する。
規約：合成の一致は厳密な等式。
使われ方：Kerodon §4.2.4（Tag 014S）、Quillen A の還元。 -/
lemma exists_leftAnodyne_leftFibration_factorization {X Y : SSet.{u}} (f : X ⟶ Y) :
    ∃ (Z : SSet.{u}) (i : X ⟶ Z) (p : Z ⟶ Y),
      Mono i ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p ∧ i ≫ p = f := by
  let d := factorizationData cofinalLeftHornFamily.rlp.llp cofinalLeftHornFamily.rlp f
  refine ⟨d.Z, d.i, d.p, cofinalLeftHornFamily_llp_rlp_le_monomorphisms _ d.hi, ?_, ?_, d.fac⟩
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions.rlp.llp d.i
    simpa only [cofinalLeftHornFamily_eq] using d.hi
  · constructor
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions.rlp d.p
    simpa only [cofinalLeftHornFamily_eq] using d.hp

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.0.0.6"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.exists_leftAnodyne_leftFibration_factorization
