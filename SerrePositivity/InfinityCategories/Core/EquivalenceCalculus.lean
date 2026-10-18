module

public import SerrePositivity.InfinityCategories.Core.FullyFaithful
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence

/-!
概要：同値の合成と二つから三つ目を得る性質。
方針：明示的な逆データと可逆二胞体の合成を使う。
規約：モデル構造の弱同値は用いない。
使われ方：Kerodon §4.5.1、Theorem 4.8.4.1 の同値の判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：関手単体集合で同型な射は一方が同値なら他方も同値。
方針：同じ逆射を使い、単位と余単位に同型を前後合成する。
規約：単なる頂点ごとの同型の族は仮定しない。
使われ方：Kerodon §4.5.1 の同値の同型不変性。 -/
lemma IsQCatEquivalence.ofFunctorIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f g : X ⟶ Y}
    (hf : IsQCatEquivalence f) (e : FunctorIso f g) : IsQCatEquivalence g := by
  obtain ⟨r, ⟨h₁⟩, ⟨h₂⟩⟩ := hf
  exact ⟨r, ⟨FunctorIso.postcomp e.symm r ≪≫ h₁⟩,
    ⟨FunctorIso.precomp e.symm r ≪≫ h₂⟩⟩

/-- 概要：同値の合成は同値。
方針：A3a の明示的な同値の合成を使う。
規約：f の後に g を適用する。
使われ方：Kerodon §4.5.1 の同値の推移性。 -/
lemma IsQCatEquivalence.comp {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsQCatEquivalence f) (hg : IsQCatEquivalence g) : IsQCatEquivalence (f ≫ g) :=
  (hf.choose.trans hg.choose).isQCatEquivalence

/-- 概要：f と f≫g が同値なら g も同値。
方針：f の逆と合成の同値を合成し、余単位で g と同型にする。
規約：三つの対象は quasicategory。
使われ方：Kerodon §4.5.1、§4.8.4 の因子分解による還元。 -/
lemma IsQCatEquivalence.cancel_left {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsQCatEquivalence f) (hfg : IsQCatEquivalence (f ≫ g)) : IsQCatEquivalence g := by
  let e := hf.choose
  have he : e.hom = f := rfl
  have h := (e.symm.trans hfg.choose).isQCatEquivalence
  have hi : FunctorIso (e.inv ≫ (f ≫ g)) g := by
    simpa only [Category.assoc, Category.id_comp, he] using FunctorIso.postcomp e.invHomIso g
  exact h.ofFunctorIso hi

/-- 概要：g と f≫g が同値なら f も同値。
方針：合成の同値と g の逆を合成し、単位で f と同型にする。
規約：三つの対象は quasicategory。
使われ方：Kerodon §4.5.1、§4.8.4 の因子分解による還元。 -/
lemma IsQCatEquivalence.cancel_right {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hg : IsQCatEquivalence g) (hfg : IsQCatEquivalence (f ≫ g)) : IsQCatEquivalence f := by
  let e := hg.choose
  have he : e.hom = g := rfl
  have h := (hfg.choose.trans e.symm).isQCatEquivalence
  have hi : FunctorIso ((f ≫ g) ≫ e.inv) f := by
    simpa only [Category.assoc, Category.comp_id, he] using FunctorIso.precomp e.homInvIso f
  exact h.ofFunctorIso hi

/-- 概要：Kan 複体間の単体的ホモトピー同値の合成は同値。
方針：quasicategory の同値に移して合成し、実際のホモトピーへ戻す。
規約：三つの単体集合の Kan 性を仮定する。
使われ方：Kerodon §4.8.3 の写像空間の合成。 -/
lemma IsSimplicialHomotopyEquivalence.comp {X Y Z : SSet.{u}}
    [KanComplex X] [KanComplex Y] [KanComplex Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsSimplicialHomotopyEquivalence f) (hg : IsSimplicialHomotopyEquivalence g) :
    IsSimplicialHomotopyEquivalence (f ≫ g) :=
  (hf.isQCatEquivalence.comp hg.isQCatEquivalence).isSimplicialHomotopyEquivalence

/-- 概要：写像空間で充満忠実な射の合成は充満忠実。
方針：各写像空間の Kan 性とホモトピー同値の合成を使う。
規約：三つの対象は quasicategory。
使われ方：Kerodon §4.8.3 の充満忠実性の合成。 -/
lemma IsFullyFaithful.comp {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsFullyFaithful f) (hg : IsFullyFaithful g) : IsFullyFaithful (f ≫ g) := by
  intro x y
  rw [pinchedHomMap_comp]
  exact (hf x y).comp (hg _ _)

end SerrePositivity.InfinityCategories
