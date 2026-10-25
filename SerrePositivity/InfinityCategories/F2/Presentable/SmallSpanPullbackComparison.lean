module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallModelFunctor
public import SerrePositivity.InfinityCategories.F2.Presentable.StrictSpanComparison

/-!
概要：共役した小さい cospan の宇宙持ち上げと、元の cospan の引き戻しを全同値で比較する。
方針：標的模型への逆同値を使う中間 cospan を置き、二つの厳密な成分同値で比較する。
規約：非厳密な余単位を辺の等式として扱わない。
使われ方：compact 成分の小さい cospan と元の引き戻しの接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：共役 cospan の大きい宇宙での引き戻しは元の cospan の引き戻しと全同値。
方針：元の三圏から標的の逆模型への厳密な比較と、始域二模型からの厳密な比較を合成する。
規約：小さい引き戻し自体の宇宙比較とは分け、元の関手を全同値の比較に保持する。
使われ方：compact な成分圏の引き戻しの小さい模型の構成。 -/
lemma exists_smallSpanPullbackComparison
    {A K L : SSet.{u}} [Quasicategory A] [Quasicategory K] [Quasicategory L]
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (e : QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A) E)
    (d : QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj K) D)
    (b : QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj L) B)
    (p : E ⟶ B) (q : D ⟶ B) :
    Nonempty (QCatEquivalence
      (F2.catPullback ((SSet.uliftFunctor.{u + 1, u}).map (smallModelFunctor e b p))
        ((SSet.uliftFunctor.{u + 1, u}).map (smallModelFunctor d b q)))
      (F2.catPullback p q)) := by
  let p₀ := (SSet.uliftFunctor.{u + 1, u}).map (smallModelFunctor e b p)
  let q₀ := (SSet.uliftFunctor.{u + 1, u}).map (smallModelFunctor d b q)
  have hp₀ : p₀ ≫ 𝟙 _ = e.hom ≫ (p ≫ b.inv) := by
    rw [Category.comp_id]
    exact smallModelFunctor_lift e b p
  have hq₀ : q₀ ≫ 𝟙 _ = d.hom ≫ (q ≫ b.inv) := by
    rw [Category.comp_id]
    exact smallModelFunctor_lift d b q
  obtain ⟨s⟩ := exists_catPullbackEquivalence_of_strictSpanEquivalence
    p₀ q₀ (p ≫ b.inv) (q ≫ b.inv) e.hom d.hom (𝟙 _)
    hp₀ hq₀ e.isQCatEquivalence d.isQCatEquivalence
    (QCatEquivalence.refl _).isQCatEquivalence
  obtain ⟨t⟩ := exists_catPullbackEquivalence_of_strictSpanEquivalence
    p q (p ≫ b.inv) (q ≫ b.inv) (𝟙 _) (𝟙 _) b.inv
    (by simp) (by simp) (QCatEquivalence.refl _).isQCatEquivalence
    (QCatEquivalence.refl _).isQCatEquivalence b.symm.isQCatEquivalence
  exact ⟨s.trans t.symm⟩

end SerrePositivity.InfinityCategories.F2.Presentable
