module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallModelFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.StrictSpanComparison

/-!
概要：共役した小さい cospan の宇宙持ち上げと、元の cospan の引き戻しを全同値で比較する。
方針：標的模型への逆同値を使う中間 cospan を置き、二つの厳密な成分同値で比較する。
規約：非厳密な余単位を辺の等式として扱わない。
使われ方：compact 成分の小さい cospan と元の引き戻しの接続。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：共役 cospan の大きい宇宙での引き戻しは元の cospan の引き戻しと全同値。
方針：元の三圏から標的の逆模型への厳密な比較と、始域二模型からの厳密な比較を合成する。
規約：小さい引き戻し自体の宇宙比較とは分け、元の関手を全同値の比較に保持する。
使われ方：compact な成分圏の引き戻しの小さい模型の構成。 -/
lemma exists_smallSpanPullbackComparison
    {A K L : SSet.{u}} [Quasicategory A] [Quasicategory K] [Quasicategory L]
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A) E)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj K) D)
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj L) B)
    (p : E ⟶ B) (q : D ⟶ B) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallModelFunctor e b p))
        ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallModelFunctor d b q)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback p q)) := by
  let p₀ := (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallModelFunctor e b p)
  let q₀ := (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallModelFunctor d b q)
  have hp₀ : p₀ ≫ 𝟙 _ = e.hom ≫ (p ≫ b.inv) := by
    rw [Category.comp_id]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallModelFunctor_lift e b p
  have hq₀ : q₀ ≫ 𝟙 _ = d.hom ≫ (q ≫ b.inv) := by
    rw [Category.comp_id]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallModelFunctor_lift d b q
  obtain ⟨s⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_catPullbackEquivalence_of_strictSpanEquivalence
    p₀ q₀ (p ≫ b.inv) (q ≫ b.inv) e.hom d.hom (𝟙 _)
    hp₀ hq₀ e.isQCatEquivalence d.isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.refl _).isQCatEquivalence
  obtain ⟨t⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_catPullbackEquivalence_of_strictSpanEquivalence
    p q (p ≫ b.inv) (q ≫ b.inv) (𝟙 _) (𝟙 _) b.inv
    (by simp) (by simp) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.refl _).isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.refl _).isQCatEquivalence b.symm.isQCatEquivalence
  exact ⟨s.trans t.symm⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
