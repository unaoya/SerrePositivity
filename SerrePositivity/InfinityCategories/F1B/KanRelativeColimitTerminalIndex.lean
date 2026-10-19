module

public import SerrePositivity.InfinityCategories.F1B.KanTerminalPointAnodyne
public import SerrePositivity.InfinityCategories.F1B.KanLeftKanIdentityVertex
public import SerrePositivity.InfinityCategories.F1B.KanRelativeColimitReindex
public import SerrePositivity.InfinityCategories.Stable.CosliceRestriction

/-!
概要：終対象への一点制限による標準相対余極限の判定。
方針：終対象包含の right anodyne 性と二つの coslice 制限の自明 Kan 性を使う。
規約：U の充填性は要求しない。
使われ方：全部分圏の像の点で Kan の相対局所余錐を恒等射の脚へ制限する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：right anodyne な添字変更は標準 U 余極限を保ち反映する。
方針：両 coslice の制限の充満忠実性と頂点全射性で相対始対象性を比較する。
規約：U に inner fibration 性を要求しない。
使われ方：終対象包含に沿う相対局所余錐の一点への還元。 -/
lemma kanIsRelativeColimitCone_iff_restrict_of_rightAnodyne
    {A J D E : SSet.{u}} [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) {p : J ⟶ D} (c : JoinCocone p) (i : A ⟶ J) [Mono i]
    (hi : rightAnodyneExtensions i) :
    IsRelativeColimitCone U c ↔ IsRelativeColimitCone U (c.restrict i) := by
  have := sliceUnderRestrict_trivialKanFibration p i hi
  have := sliceUnderRestrict_trivialKanFibration (p ≫ U) i hi
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section (sliceUnderRestrict p i)
  have hsurj : Function.Surjective ((sliceUnderRestrict p i).app (Opposite.op ⦋0⦌)) := by
    intro y
    exact ⟨s.app (Opposite.op ⦋0⦌) y,
      ConcreteCategory.congr_hom (NatTrans.congr_app hs (Opposite.op ⦋0⦌)) y⟩
  exact kanRelativeInitialVertex_iff_of_comparison
    (sliceUnderPostcomp p U) (sliceUnderPostcomp (i ≫ p) U)
    (sliceUnderRestrict p i) (sliceUnderRestrict (p ≫ U) i)
    (sliceUnderRestrict_postcomp p i U).symm
    (isQCatEquivalence_of_trivialKanFibration _).isFullyFaithful
    (isQCatEquivalence_of_trivialKanFibration _).isFullyFaithful hsurj c

/-- 概要：終対象を持つ添字上の標準相対余極限はその終対象での脚で判定できる。
方針：終対象を選ぶ一点の包含に沿って相対余錐を制限する。
規約：添字 J の quasicategory 性は不要。
使われ方：Kan 単位の可逆性のための局所入力を一点図式へ移す。 -/
lemma kanIsRelativeColimitCone_iff_restrict_terminal {J D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E)
    {p : J ⟶ D} (c : JoinCocone p) (t : J _⦋0⦌) (ht : IsTerminalVertex t) :
    IsRelativeColimitCone U c ↔ IsRelativeColimitCone U (c.restrict (SSet.yonedaEquiv.symm t)) := by
  have := cofinalPointInclusion_mono t
  exact kanIsRelativeColimitCone_iff_restrict_of_rightAnodyne U c _
    (kanTerminalPoint_rightAnodyne ht)

/-- 概要：充満忠実な inner 包含の像では標準相対 Kan 余錐を恒等射の脚で判定できる。
方針：局所添字の恒等射の終対象性を一点制限の判定へ渡す。
規約：元の図式 F₀ と候補の頂点を保つ同じ余錐を制限する。
使われ方：相対 Kan の局所条件から単位の成分の可逆性を導く。 -/
lemma kanLeftLocalColimit_iff_restrict_identity {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (δ : K ⟶ C) [InnerFibration δ] (hδ : IsFullyFaithful δ) (U : D ⟶ E)
    (F₀ : K ⟶ D) (k : K _⦋0⦌)
    (c : JoinCocone (leftKanDiagram δ F₀ (δ.app (Opposite.op ⦋0⦌) k))) :
    IsRelativeColimitCone U c ↔
      IsRelativeColimitCone U (c.restrict (SSet.yonedaEquiv.symm (kanLeftKanIdentityVertex δ k))) :=
  kanIsRelativeColimitCone_iff_restrict_terminal U c _ (kanLeftKanIdentityVertex_isTerminal δ hδ k)

end SerrePositivity.InfinityCategories.F1B
