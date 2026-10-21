module

public import SerrePositivity.InfinityCategories.F1.FunctorIsoPrecompositionProjection
public import SerrePositivity.InfinityCategories.F1.FunctorIsoSquareIdentity

/-!
概要：指定された逆向き二因子の貼り合わせを、元の前合成・二回の後合成と照合する。
方針：前後合成の交換と三端点の同じ表示への移送を使う。
規約：元の指定同型とその合成を保持する。
使われ方：既存の局所結合比較と元の全 Hom 上の指定因子の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 逆向きの指定二因子は、同じ三端点と指定値を保って前合成できる。 -/
lemma functorIso_precomp_inverse_paste_heq {H X K : SSet.{u}}
    {f g h : H ⟶ X} (e : FunctorIso f g) (d : FunctorIso f h) (r : K ⟶ H)
    {a b c : K ⟶ X} (E : FunctorIso a b) (N : FunctorIso a c)
    (hf : (e.precomp r).sourceMap = E.sourceMap)
    (hg : (e.precomp r).targetMap = E.targetMap)
    (hh : (d.precomp r).targetMap = N.targetMap)
    (he : HEq E (e.precomp r)) (hd : HEq N (d.precomp r)) :
    HEq (FunctorIso.precomp (e.symm ≪≫ d) r) (E.symm ≪≫ N) := by
  change r ≫ f = a at hf
  change r ≫ g = b at hg
  change r ≫ h = c at hh
  subst a b c
  cases eq_of_heq he
  cases eq_of_heq hd
  rw [F2.functorIso_precomp_trans, F2.functorIso_precomp_symm]

/-- 元の二回の後合成と前合成は、始点正規化後も同じ指定値を回収する。 -/
lemma functorIso_normalized_postcomp_precomp_twice_heq {H X Y Z K : SSet.{u}}
    {f g : H ⟶ X} (e : FunctorIso f g) (r : K ⟶ H) (p : X ⟶ Y) (q : Y ⟶ Z)
    {f' : H ⟶ Z} (hf : f ≫ (p ≫ q) = f') :
    HEq (((e.precomp r).postcomp p).postcomp q)
      ((F2.functorIsoOfEq (e.postcomp (p ≫ q)) hf rfl).precomp r) := by
  have h := (F2.functorIso_postcomp_postcomp (e.precomp r) p q).trans
    (F2.functorIso_precomp_postcomp e r (p ≫ q))
  exact HEq.trans (heq_of_eq h)
    (functorIsoOfEq_precomp_heq (e.postcomp (p ≫ q)) hf rfl r).symm

/-- 同じ前後合成の交換は、始点だけを正規化した後の終点作用も保持する。 -/
lemma functorIso_normalized_postcomp_precomp_twice_target
    {H X Y Z K : SSet.{u}} {f g : H ⟶ X}
    (e : FunctorIso f g) (r : K ⟶ H) (p : X ⟶ Y) (q : Y ⟶ Z)
    {f' : H ⟶ Z} (hf : f ≫ (p ≫ q) = f') :
    ((F2.functorIsoOfEq (e.postcomp (p ≫ q)) hf rfl).precomp r).targetMap =
      (((e.precomp r).postcomp p).postcomp q).targetMap := by
  simp only [FunctorIso.targetMap, Category.assoc]

/-- 同じ指定二因子の合成は、三端点と前合成した指定値を保って貼り合う。 -/
lemma functorIso_precomp_paste_heq {H X K : SSet.{u}}
    {f g h : H ⟶ X} (e : FunctorIso f g) (d : FunctorIso g h) (r : K ⟶ H)
    {a b c : K ⟶ X} (E : FunctorIso a b) (N : FunctorIso b c)
    (hf : (e.precomp r).sourceMap = E.sourceMap)
    (hg : (e.precomp r).targetMap = E.targetMap)
    (hh : (d.precomp r).targetMap = N.targetMap)
    (he : HEq E (e.precomp r)) (hd : HEq N (d.precomp r)) :
    HEq (FunctorIso.precomp (e ≪≫ d) r) (E ≪≫ N) := by
  change r ≫ f = a at hf
  change r ≫ g = b at hg
  change r ≫ h = c at hh
  subst a b c
  cases eq_of_heq he
  cases eq_of_heq hd
  rw [F2.functorIso_precomp_trans]

end SerrePositivity.InfinityCategories
