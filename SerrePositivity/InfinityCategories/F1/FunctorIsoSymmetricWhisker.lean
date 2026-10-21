module

public import SerrePositivity.InfinityCategories.F1.FunctorIsoWhiskeredPasting

/-!
概要：指定制限自然性の逆を、元の二段の前合成と始点正規化の表示で回収する。
方針：逆同型の前合成則と指定値を保つ端点正規化を使う。
規約：元の同型とその逆の指定値を保持する。
使われ方：既存の局所制限自然性と三辺の第二因子の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 端点だけの表示変更は、元の指定逆同型を保持する。 -/
lemma functorIsoOfEq_symm_heq {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (e : FunctorIso f g) (hf : f = f') (hg : g = g') :
    HEq (F2.functorIsoOfEq e hf hg).symm e.symm := by
  subst f' g'
  rfl

/-- 二段の前合成と始点だけの正規化は、指定逆同型の同じ値を回収する。 -/
lemma functorIso_normalized_symm_precomp_precomp_heq
    {H X Y K : SSet.{u}} {f g : X ⟶ Y}
    (e : FunctorIso f g) (p : H ⟶ X) (q : K ⟶ H)
    {g₀ : H ⟶ Y} (hg : p ≫ g = g₀)
    {f₁ : K ⟶ Y} (hf : (q ≫ p) ≫ f = f₁) :
    HEq ((F2.functorIsoOfEq (FunctorIso.precomp e.symm p) hg rfl).precomp q)
      (F2.functorIsoOfEq (e.precomp (q ≫ p)) hf rfl).symm := by
  have h₀ := functorIsoOfEq_precomp_precomp_heq e.symm p hg rfl q
  have h₁ := heq_of_eq (F2.functorIso_precomp_symm e (q ≫ p))
  have h₂ := functorIsoOfEq_symm_heq (e.precomp (q ≫ p)) hf rfl
  exact HEq.trans h₀ (HEq.trans h₁ h₂.symm)

/-- 同じ逆自然性の二段の前合成は、始点正規化した自然性の始点へ戻る。 -/
lemma functorIso_normalized_symm_precomp_precomp_target
    {H X Y K : SSet.{u}} {f g : X ⟶ Y}
    (e : FunctorIso f g) (p : H ⟶ X) (q : K ⟶ H)
    {g₀ : H ⟶ Y} (hg : p ≫ g = g₀)
    {f₁ : K ⟶ Y} (hf : (q ≫ p) ≫ f = f₁) :
    ((F2.functorIsoOfEq (FunctorIso.precomp e.symm p) hg rfl).precomp q).targetMap =
      (F2.functorIsoOfEq (e.precomp (q ≫ p)) hf rfl).sourceMap := by
  exact (Category.assoc _ _ _).symm.trans hf

/-- 前後合成の交換は、同じ指定同型の両端の作用を回収する。 -/
lemma FunctorIso.postcomp_precomp_endpoints {H X Y K : SSet.{u}} {f g : H ⟶ X}
    (e : FunctorIso f g) (r : K ⟶ H) (p : X ⟶ Y) :
    ((e.postcomp p).precomp r).sourceMap = ((e.precomp r).postcomp p).sourceMap ∧
    ((e.postcomp p).precomp r).targetMap = ((e.precomp r).postcomp p).targetMap := by
  simp only [sourceMap, targetMap, Category.assoc, and_self]

end SerrePositivity.InfinityCategories
