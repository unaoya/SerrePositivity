module

public import SerrePositivity.InfinityCategories.F2.FunctorIsoChainTransport
public import SerrePositivity.InfinityCategories.F2.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.F2.UniverseDownFunctorCancellation

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

/-- 指定同型の二段の前合成は、元の合成射による前合成そのものである。 -/
lemma functorIso_precomp_precomp {A B X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : FunctorIso f g) (p : B ⟶ X) (q : A ⟶ B) :
    (e.precomp p).precomp q = e.precomp (q ≫ p) := by
  have hn : (pre (q ≫ p)).app Y = (pre p).app Y ≫ (pre q).app Y := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    apply CategoryTheory.Functor.functorHom_ext
    intro d α
    rfl
  have hh := congrArg (fun k => SSet.mapHomotopyCategory k) hn
  rw [mapHomotopyCategory_comp_eq] at hh
  simp only [functorIso_precomp_eq_mapIso]
  exact (eq_of_heq (mapIso_heq_of_functor_eq hh e)).symm

/-- 元の前合成射の等式は指定同型の前合成の値を型付きで保つ。 -/
lemma functorIso_precomp_heq_of_map_eq {A X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : FunctorIso f g) {p q : A ⟶ X} (h : p = q) :
    HEq (e.precomp p) (e.precomp q) := by cases h; rfl

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

end SerrePositivity.InfinityCategories.F2
