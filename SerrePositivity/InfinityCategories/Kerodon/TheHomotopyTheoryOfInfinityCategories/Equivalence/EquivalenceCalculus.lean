module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：同値の合成と二つから三つ目を得る性質。
方針：明示的な逆データと可逆二胞体の合成を使う。
規約：モデル構造の弱同値は用いない。
使われ方：Kerodon §4.5.1（Tag 01DQ）、Theorem 4.8.4.1（Tag 01JX） の同値の判定。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：関手単体集合で同型な射は一方が同値なら他方も同値。
方針：同じ逆射を使い、単位と余単位に同型を前後合成する。
規約：単なる頂点ごとの同型の族は仮定しない。
使われ方：Kerodon §4.5.1（Tag 01DQ） の同値の同型不変性。 -/
@[kerodon 033Z]
lemma IsQCatEquivalence.ofFunctorIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f g : X ⟶ Y}
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence g := by
  obtain ⟨r, ⟨h₁⟩, ⟨h₂⟩⟩ := hf
  exact ⟨r, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e.symm r ≪≫ h₁⟩,
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e.symm r ≪≫ h₂⟩⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence (ofFunctorIso)


/-- 概要：同値の合成は同値。
方針：A3a の明示的な同値の合成を使う。
規約：f の後に g を適用する。
使われ方：Kerodon §4.5.1（Tag 01DQ） の同値の推移性。 -/
lemma IsQCatEquivalence.comp {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f) (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence g) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (f ≫ g) :=
  (hf.choose.trans hg.choose).isQCatEquivalence

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence (comp)


/-- 概要：f と f≫g が同値なら g も同値。
方針：f の逆と合成の同値を合成し、余単位で g と同型にする。
規約：三つの対象は quasicategory。
使われ方：Kerodon §4.5.1（Tag 01DQ）、§4.8.4（Tag 06SQ） の因子分解による還元。 -/
lemma IsQCatEquivalence.cancel_left {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f) (hfg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (f ≫ g)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence g := by
  let e := hf.choose
  have he : e.hom = f := rfl
  have h := (e.symm.trans hfg.choose).isQCatEquivalence
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (e.inv ≫ (f ≫ g)) g := by
    simpa only [Category.assoc, Category.id_comp, he] using _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e.invHomIso g
  exact h.ofFunctorIso hi

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence (cancel_left)


/-- 概要：g と f≫g が同値なら f も同値。
方針：合成の同値と g の逆を合成し、単位で f と同型にする。
規約：三つの対象は quasicategory。
使われ方：Kerodon §4.5.1（Tag 01DQ）、§4.8.4（Tag 06SQ） の因子分解による還元。 -/
lemma IsQCatEquivalence.cancel_right {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence g) (hfg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (f ≫ g)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f := by
  let e := hg.choose
  have he : e.hom = g := rfl
  have h := (hfg.choose.trans e.symm).isQCatEquivalence
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((f ≫ g) ≫ e.inv) f := by
    simpa only [Category.assoc, Category.comp_id, he] using _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e.homInvIso f
  exact h.ofFunctorIso hi

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence (cancel_right)


/-- 概要：Kan 複体間の単体的ホモトピー同値の合成は同値。
方針：quasicategory の同値に移して合成し、実際のホモトピーへ戻す。
規約：三つの単体集合の Kan 性を仮定する。
使われ方：Kerodon §4.8.3（Tag 05AW） の写像空間の合成。 -/
lemma IsSimplicialHomotopyEquivalence.comp {X Y Z : SSet.{u}}
    [KanComplex X] [KanComplex Y] [KanComplex Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f) (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (f ≫ g) :=
  (hf.isQCatEquivalence.comp hg.isQCatEquivalence).isSimplicialHomotopyEquivalence

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsSimplicialHomotopyEquivalence (comp)


/-- 概要：写像空間で充満忠実な射の合成は充満忠実。
方針：各写像空間の Kan 性とホモトピー同値の合成を使う。
規約：三つの対象は quasicategory。
使われ方：Kerodon §4.8.3（Tag 05AW） の充満忠実性の合成。 -/
lemma IsFullyFaithful.comp {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f) (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful g) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (f ≫ g) := by
  intro x y
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap_comp]
  exact (hf x y).comp (hg _ _)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsFullyFaithful (comp)


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
