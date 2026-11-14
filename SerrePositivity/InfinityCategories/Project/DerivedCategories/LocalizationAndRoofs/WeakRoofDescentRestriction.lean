module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.WeakRoofDescentSpace

/-! # 降下空間全体上の固定 Hom への coherent な制限

概要：二つの可換正方形から、降下の全高次族の固定 Hom への制限を一つの関手同型で比較する。
方針：二段降下の普遍比較を内部 Hom の前合成で写し、可換性の厳密な等式を使う。
規約：パラメータを個別に選ばない。使われ方：商 Hom への作用と元の作用の全高次の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalClosed SSet

/-- 屋根から降下した写像を、指定された固定 Hom 上へ制限する全高次族。 -/
def weakRoofDescentAction {R Q E Z H : SSet.{u}} (w : R ⟶ Q) (i : Z ⟶ E)
    (t : R ⟶ E) (j : H ⟶ Q) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescentSpace w i t ⟶ (ihom H).obj Z :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescentExtension w i t ≫ (pre j).app Z

/-- 全高次の降下作用は、元の固定 Hom 上で指定された作用と coherent に一致する。 -/
def weakRoofDescentRestrictionIso {R Q E Z H H₀ : SSet.{u}} [KanComplex Z]
    (w : R ⟶ Q) (i : Z ⟶ E) (t : R ⟶ E)
    (k : H₀ ⟶ R) (l : H₀ ⟶ H) (j : H ⟶ Q) (n : H₀ ⟶ Z)
    (hw : k ≫ w = l ≫ j) (ht : k ≫ t = n ≫ i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (weakRoofDescentAction w i t j ≫ (pre l).app Z)
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex n)) := by
  have hpw : (pre w).app Z ≫ (pre k).app Z = (pre j).app Z ≫ (pre l).app Z := by
    rw [← NatTrans.comp_app, ← pre_map, hw, pre_map, NatTrans.comp_app]
  have hpt : (pre t).app Z ≫ (pre k).app Z = (pre i).app Z ≫ (pre n).app Z := by
    rw [← NatTrans.comp_app, ← pre_map, ht, pre_map, NatTrans.comp_app]
  have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescentExtensionIso w i t) ((pre k).app Z)
  simp only [Category.assoc] at h₁
  rw [hpw, hpt] at h₁
  have h₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescentEvaluationIso w i t) ((pre n).app Z)
  have hc : SSet.const (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescentSpace w i t) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 Z)) ≫
      (pre n).app Z =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex n) := by
    rw [SSet.const_comp]
    change SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (n ≫ 𝟙 Z)) = _
    rw [Category.comp_id]
  rw [hc] at h₂
  simp only [Category.assoc] at h₂
  simpa only [weakRoofDescentAction, Category.assoc] using h₁ ≪≫ h₂

end SerrePositivity.InfinityCategories.Project.DerivedCategories
