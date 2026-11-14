module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.WeakRoofDescentFamilyEvaluation
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalClosed SSet
/-- 全空間上の制限同型は、任意の元の族を同じ選択空間上で評価する。 -/
def functorRestrictionFamilyIso {S R Q Z K : SSet.{u}}
    (A : S ⟶ (ihom Q).obj Z) (q : R ⟶ Q) (G : R ⟶ Z)
    (I : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (A ≫ (pre q).app Z) (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)))
    (a : K ⟶ R) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (A ≫ (pre (a ≫ q)).app Z)
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (a ≫ G))) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp I ((pre a).app Z)
  have hc : SSet.const (X := S) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) ≫ (pre a).app Z =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (a ≫ G)) := by
    rw [SSet.const_comp]
    rfl
  rw [hc] at h
  simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPrecomposition_comp] using h
/-- 指定した二つの族の厳密表示を使って、同じ全空間上の制限同型を読む。 -/
def functorRestrictionFamilyIso_of_eq {S R Q Z K : SSet.{u}}
    (A : S ⟶ (ihom Q).obj Z) (q : R ⟶ Q) (G : R ⟶ Z)
    (I : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (A ≫ (pre q).app Z) (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)))
    (a : K ⟶ R) (b : K ⟶ Q) (c : K ⟶ Z) (hb : a ≫ q = b) (hc : a ≫ G = c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (A ≫ (pre b).app Z) (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c)) := by
  subst b
  subst c
  exact functorRestrictionFamilyIso A q G I a
end SerrePositivity.InfinityCategories.Project.DerivedCategories
