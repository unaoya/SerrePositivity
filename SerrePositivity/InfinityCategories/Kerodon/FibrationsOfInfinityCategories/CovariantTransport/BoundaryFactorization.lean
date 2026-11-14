module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms
public import Mathlib.CategoryTheory.SmallObject.Basic

/-!
概要：単体集合の射の単射と trivial Kan fibration への因子分解。
方針：有限な境界の包含に小対象論法を適用し、左因子の単射性を閉性から得る。
規約：境界包含と持ち上げ性だけを使う。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、写像円柱比較の単射性の仮定の除去。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：全次元の標準境界の包含からなる射の性質。
方針：自然数で添字づけた射の族を使う。
規約：零次元の空境界も含む。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、trivial Kan fibration の小対象論法。 -/
def boundaryInclusions : MorphismProperty SSet.{u} :=
  .ofHoms (fun n : ℕ ↦ (boundary.{u} n).ι)

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

/-- 概要：境界包含の族は小対象論法のために小さい。
方針：自然数で添字づけた族の小ささを使う。
規約：単体集合と同じ宇宙で測る。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、因子分解の存在。 -/
instance boundaryInclusions_isSmall : MorphismProperty.IsSmall.{u} boundaryInclusions.{u} :=
  isSmall_ofHoms ..

/-- 概要：境界包含には可算小対象論法を適用できる。
方針：各境界が有限表示可能であることを使う。
規約：反復を制御する基数は aleph0。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、境界を付け加える因子分解。 -/
instance boundaryInclusions_isCardinalForSmallObjectArgument :
    IsCardinalForSmallObjectArgument boundaryInclusions.{u} Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      obtain ⟨n⟩ := hi
      infer_instance
    infer_instance

/-- 概要：境界包含の族は小対象論法を満たす。
方針：可算反復の基数条件を取り出す。
規約：関手的な因子分解が得られる。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、単射と trivial Kan fibration の分離。 -/
instance boundaryInclusions_hasSmallObjectArgument : HasSmallObjectArgument.{u} boundaryInclusions.{u} :=
  ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

/-- 概要：境界包含に対する右持ち上げ性は trivial Kan fibration 性と一致する。
方針：全境界による既存の判定を使う。
規約：右辺は単射全体に対する右持ち上げ性。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、因子分解の右因子の判定。 -/
lemma boundaryInclusions_rlp_eq : boundaryInclusions.{u}.rlp = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations := by
  ext X Y p
  constructor
  · intro h
    exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary p).mpr (fun n ↦ h _ ⟨n⟩)).mem
  · intro h
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p := ⟨h⟩
    rintro A B i ⟨n⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := p) _ inferInstance

/-- 概要：境界包含の右持ち上げ性に対し左持ち上げ性を持つ射は単射。
方針：小対象論法のセル分解を使い、単射の余積・押し出し・超限合成・retract による閉性を使う。
規約：右持ち上げ性は全境界に対して取る。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、因子分解の左因子の判定。 -/
lemma boundaryInclusions_llp_rlp_le_monomorphisms :
    boundaryInclusions.{u}.rlp.llp ≤ monomorphisms SSet := by
  rw [llp_rlp_of_hasSmallObjectArgument]
  rw [retracts_le_iff, transfiniteCompositions_le_iff, pushouts_le_iff, coproducts_le_iff]
  rintro X Y f ⟨n⟩
  exact monomorphisms.infer_property _

/-- 概要：単体集合の任意の射は単射と trivial Kan fibration の合成に分解できる。
方針：境界包含の小対象論法の因子分解を取り、両因子の判定を適用する。
規約：分解の等式は厳密な射の等式。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、構造射の単射性の仮定を外す。 -/
lemma exists_mono_trivialKan_factorization {X Y : SSet.{u}} (f : X ⟶ Y) :
    ∃ (Z : SSet.{u}) (i : X ⟶ Z) (p : Z ⟶ Y), Mono i ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p ∧ i ≫ p = f := by
  let d := factorizationData boundaryInclusions.rlp.llp boundaryInclusions.rlp f
  refine ⟨d.Z, d.i, d.p, ?_, ?_, d.fac⟩
  · exact boundaryInclusions_llp_rlp_le_monomorphisms _ d.hi
  · constructor
    rw [← boundaryInclusions_rlp_eq]
    exact d.hp

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.0.0.2"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.boundaryInclusions_rlp_eq
attribute [cite HTT "2.0.0.6"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.exists_mono_trivialKan_factorization
