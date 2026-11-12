module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceTwoOfSix
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulEquivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：同値の写像空間上の充満忠実性と同値判定の両方向。
方針：逆射との二つの合成を恒等と比較し、写像空間の二対六則を使う。
規約：写像空間のホモトピー圏への弱化は行わない。
使われ方：Kerodon Theorem 4.8.4.1（Tag 01JX）、Remark 4.8.3.9（Tag 059X）。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：quasicategory の同値は右 pinched 写像空間で充満忠実。
方針：逆射との合成の充満忠実性と写像空間の二対六則から結論する。
規約：実際の単体的ホモトピー逆の存在を結論にする。
使われ方：Kerodon Theorem 4.8.4.1（Tag 01JX） の必要条件。 -/
@[kerodon 06QP]
lemma IsQCatEquivalence.isFullyFaithful {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f := by
  obtain ⟨g, ⟨e₀⟩, ⟨e₁⟩⟩ := he
  have hfg := e₀.isFullyFaithful_iff.mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_id X)
  have hgf := e₁.isFullyFaithful_iff.mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_id Y)
  intro x y
  have ha := hfg x y
  have hb := hgf (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap_comp] at ha hb
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isSimplicialHomotopyEquivalence_of_composites ha hb).cancel_right ha

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsQCatEquivalence (isFullyFaithful)


/-- 概要：明示的な同値の順方向の射は充満忠実。
方針：逆データを存在量化した同値性の結論を使う。
規約：両端は quasicategory。
使われ方：Kerodon §4.8.3（Tag 05AW） の写像空間の比較。 -/
lemma QCatEquivalence.isFullyFaithful {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful e.hom :=
  e.isQCatEquivalence.isFullyFaithful

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.QCatEquivalence (isFullyFaithful)


/-- 概要：同値であることは充満忠実かつ本質的全射であることと同値。
方針：主判定と逆データからの二つの必要条件を組み合わせる。
規約：充満忠実性は全ての右 pinched 写像空間の実際のホモトピー同値。
使われ方：Kerodon Theorem 4.8.4.1（Tag 01JX） の完全な判定。 -/
lemma isQCatEquivalence_iff_fullyFaithful_essentiallySurjective {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective f :=
  ⟨fun he ↦ ⟨he.isFullyFaithful, he.choose.isEssentiallySurjective⟩,
    fun h ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective f h.1 h.2⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
