module
public import SerrePositivity.InfinityCategories.Derived.WeakRoofDescentFamilyEvaluation
/-!
概要：全選択空間上の作用の制限同型を、任意の元の Hom 族への制限に移す。
方針：前合成の結合則と定値関手頂点の公式を使う。
規約：元の一つの制限同型を全族で共有する。使われ方：全選択空間上の単位の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet
/-- 全空間上の制限同型は、任意の元の族を同じ選択空間上で評価する。 -/
def functorRestrictionFamilyIso {S R Q Z K : SSet.{u}}
    (A : S ⟶ (ihom Q).obj Z) (q : R ⟶ Q) (G : R ⟶ Z)
    (I : FunctorIso (A ≫ (pre q).app Z) (SSet.const (functorVertex G)))
    (a : K ⟶ R) :
    FunctorIso (A ≫ (pre (a ≫ q)).app Z)
      (SSet.const (functorVertex (a ≫ G))) := by
  have h := FunctorIso.postcomp I ((pre a).app Z)
  have hc : SSet.const (X := S) (functorVertex G) ≫ (pre a).app Z =
      SSet.const (functorVertex (a ≫ G)) := by
    rw [SSet.const_comp]
    rfl
  rw [hc] at h
  simpa only [Category.assoc, roofPrecomposition_comp] using h
/-- 指定した二つの族の厳密表示を使って、同じ全空間上の制限同型を読む。 -/
def functorRestrictionFamilyIso_of_eq {S R Q Z K : SSet.{u}}
    (A : S ⟶ (ihom Q).obj Z) (q : R ⟶ Q) (G : R ⟶ Z)
    (I : FunctorIso (A ≫ (pre q).app Z) (SSet.const (functorVertex G)))
    (a : K ⟶ R) (b : K ⟶ Q) (c : K ⟶ Z) (hb : a ≫ q = b) (hc : a ≫ G = c) :
    FunctorIso (A ≫ (pre b).app Z) (SSet.const (functorVertex c)) := by
  subst b
  subst c
  exact functorRestrictionFamilyIso A q G I a
end SerrePositivity.InfinityCategories
