module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.MappingSpaceTrivialFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus

/-!
概要：Kan 複体のホモトピー同値と充満忠実性の消去則。
方針：実際のホモトピー逆の二対三則を右写像空間の合成に適用する。
規約：充満忠実な後合成による検出を扱う。
使われ方：Kerodon §4.8.3（Tag 05AW）–4.8.4（Tag 06SQ） の可逆 path を介した充満忠実性。

対応節は Kerodon 4.8（Tag 0578）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors

/-- 概要：Kan 複体間のホモトピー同値は後合成側で消去できる。
方針：quasicategory の同値の二対三則へ移し、実際のホモトピー逆へ戻す。
規約：三つの対象の Kan 性を仮定する。
使われ方：Kerodon §4.8.3（Tag 05AW） の写像空間の消去則。 -/
lemma IsSimplicialHomotopyEquivalence.cancel_right {X Y Z : SSet.{u}}
    [KanComplex X] [KanComplex Y] [KanComplex Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence g) (hfg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (f ≫ g)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f :=
  (hg.isQCatEquivalence.cancel_right hfg.isQCatEquivalence).isSimplicialHomotopyEquivalence

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsSimplicialHomotopyEquivalence (cancel_right)


/-- 概要：Kan 複体間のホモトピー同値は前合成側で消去できる。
方針：quasicategory の同値の二対三則へ移し、実際のホモトピー逆へ戻す。
規約：三つの対象の Kan 性を仮定する。
使われ方：Kerodon §4.8.3（Tag 05AW） の写像空間の二対三則。 -/
lemma IsSimplicialHomotopyEquivalence.cancel_left {X Y Z : SSet.{u}}
    [KanComplex X] [KanComplex Y] [KanComplex Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f) (hfg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (f ≫ g)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence g :=
  (hf.isQCatEquivalence.cancel_left hfg.isQCatEquivalence).isSimplicialHomotopyEquivalence

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsSimplicialHomotopyEquivalence (cancel_left)


/-- 概要：充満忠実な射による後合成は充満忠実性を検出する。
方針：右写像空間の合成に Kan 複体のホモトピー同値の消去則を適用する。
規約：全ての単体集合が quasicategory。
使われ方：Kerodon §4.8.4（Tag 06SQ） の path の二端点の評価。 -/
lemma IsFullyFaithful.cancel_right {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful g) (hfg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (f ≫ g)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f := by
  intro x y
  have h := hfg x y
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap_comp] at h
  exact (hg (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)).cancel_right h

/-- 概要：充満忠実な後合成の前後で充満忠実性は同値。
方針：合成の閉性と後合成の消去則を組み合わせる。
規約：三つの対象は quasicategory。
使われ方：Kerodon §4.8.4（Tag 06SQ） の可逆 path の評価。 -/
lemma isFullyFaithful_comp_iff {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful g) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (f ≫ g) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f :=
  ⟨hg.cancel_right, fun hf ↦ hf.comp hg⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
