module
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FunctorIsoChainTransport
public import SerrePositivity.InfinityCategories.Core.FunctorIsoTransport
public import SerrePositivity.InfinityCategories.Core.FunctorIsoWhiskerCancellation
public import SerrePositivity.InfinityCategories.Core.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Core.FunctorIsoWhiskerUnit
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorEqIsoTransport


/-!
概要：指定同型の二段の前合成と、標的表示の往復を指定値を保って簡約する。
方針：関手空間の前合成の合成則と、明示した同型の往復の等式を使う。
規約：端点を明示して指定類を保持。使われ方：共通の左脚の底の指定像の正規化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 標的同型とその逆で後合成すると元の指定同型の値を回収する。 -/
lemma functorIso_postcomp_iso_cancel {A X Y : SSet.{u}} {f g : A ⟶ X}
    (e : FunctorIso f g) (i : X ≅ Y) : HEq ((e.postcomp i.hom).postcomp i.inv) e := by
  have ht := functorIso_postcomp_postcomp e i.hom i.inv
  have hm := functorIso_postcomp_heq_of_map_eq e i.hom_inv_id.symm
  exact (heq_of_eq ht).trans (hm.trans (heq_of_eq (functorIso_postcomp_id e)))

/-- 明示した端点補正は、同じ逆同型の前後合成の指定値も保持する。 -/
lemma functorIsoOfEq_symm_precomp_postcomp_heq {A X Y Z : SSet.{u}}
    {f g f' g' : X ⟶ Y} (e : FunctorIso f g) (hf : f = f') (hg : g = g')
    (p : A ⟶ X) (q : Y ⟶ Z) :
    HEq ((FunctorIso.precomp (functorIsoOfEq e hf hg).symm p).postcomp q)
      ((FunctorIso.precomp e.symm p).postcomp q) := by
  subst f' g'
  rfl

/-- 二段の制限と値比較の像を、明示した入力射の等式で一度に正規化する。 -/
lemma functorIso_precomp_precomp_postcomp_heq {A B X Y Z : SSet.{u}}
    {f g : X ⟶ Y} {f' g' : X ⟶ Z}
    (e : FunctorIso f g) (d : FunctorIso f' g')
    (p : B ⟶ X) (q : A ⟶ B) (r : A ⟶ X) (w : Y ⟶ Z)
    (hf : f' = f ≫ w) (hg : g' = g ≫ w)
    (he : HEq (e.postcomp w) d) (hr : q ≫ p = r) :
    HEq (((e.precomp p).precomp q).postcomp w) (d.precomp r) := by
  rw [functorIso_precomp_precomp, functorIso_precomp_postcomp]
  have h := functorIso_precomp_heq_of_heq d (e.postcomp w) hf hg he (q ≫ p)
  exact h.trans (functorIso_precomp_heq_of_map_eq d hr)

/-- 指定正方形の共通の前置同型を、その逆との合成で消去する。 -/
lemma functorIso_cancel_inverse_prefix {A X : SSet.{u}} {f g h i j k : A ⟶ X}
    (n : FunctorIso f g) (a : FunctorIso f h) (b : FunctorIso h i)
    (c : FunctorIso i j) (d : FunctorIso g k) (e : FunctorIso k j)
    (hs : a ≪≫ b ≪≫ c = n ≪≫ d ≪≫ e) :
    (n.symm ≪≫ a) ≪≫ b ≪≫ c = d ≪≫ e := by
  calc
    _ = n.symm ≪≫ (a ≪≫ b ≪≫ c) := by simp only [Iso.trans_assoc]
    _ = n.symm ≪≫ (n ≪≫ d ≪≫ e) := congrArg (fun t => n.symm ≪≫ t) hs
    _ = _ := by simp only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]

end SerrePositivity.InfinityCategories.F2
