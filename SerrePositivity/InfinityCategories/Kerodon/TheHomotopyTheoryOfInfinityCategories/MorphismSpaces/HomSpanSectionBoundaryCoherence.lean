module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomSpanSectionBoundaryIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomSpanSectionFactorCoherence

/-!
概要：元の span の指定境界比較の前合成は、同じ始域からの因子比較そのもの。
方針：恒等始域での端点正規化を保ち、因子比較の前合成則を使う。
規約：元の指定切断と境界比較を選び直さない。
使われ方：輸送正方形の境界を元の大域 Hom 自然性に同定する。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 指定境界比較を共通始域から引き戻すと、同じ切断による元の因子比較になる。 -/
lemma homSpanSectionBoundaryIso_precomp {P X Y H : SSet.{u}}
    [Quasicategory P] [Quasicategory X] [Quasicategory Y] [Quasicategory H]
    (p : P ⟶ X) (q : P ⟶ Y) (s : X ⟶ P) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful p)
    (hs : s ≫ p = 𝟙 X) (r : H ⟶ P) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionBoundaryIso p q s hp hs).precomp r =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionTransportFactorIso p q s hp hs r := by
  have he := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionTransportFactorIso p q s hp hs (𝟙 P))
    (by rw [Category.id_comp]) (Category.id_comp q)
  have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_precomp_heq_of_heq _ _
    (by rw [Category.id_comp]) (Category.id_comp q) he r
  exact eq_of_heq (hh.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionTransportFactorIso_precomp_heq
    p q s hp hs (𝟙 P) r r (Category.comp_id r)))

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
