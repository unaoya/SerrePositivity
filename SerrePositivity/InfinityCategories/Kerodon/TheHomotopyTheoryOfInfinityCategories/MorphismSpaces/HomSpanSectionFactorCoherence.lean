module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerCancellation

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomSpanSectionTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIsoTransport

/-!
概要：既存の span 輸送比較は同じ切断の単位の前後合成そのもの。
方針：両端の表示の輸送だけを取り除く。
規約：元の指定された比較の値を保持する。
使われ方：大域自然性と輸送三角形を同じ単位比較で照合する。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 既存の span 輸送比較は、単位の前後合成を端点正規化したもの。 -/
lemma homSpanSectionTransportFactorIso_heq
    {P X Y H : SSet.{u}} [Quasicategory P] [Quasicategory X]
    [Quasicategory Y] [Quasicategory H]
    (p : P ⟶ X) (q : P ⟶ Y) (s : X ⟶ P) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful p)
    (hs : s ≫ p = 𝟙 X) (r : H ⟶ P) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionTransportFactorIso p q s hp hs r)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionSourceIso p s hp hs).postcomp q).precomp r) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionSourceIso p s hp hs).postcomp q) r)
    (by simp only [Category.assoc]) (by rw [Category.id_comp])

/-- 同じ因子比較の前合成は、合成した元の共通始域からの因子比較そのもの。 -/
lemma homSpanSectionTransportFactorIso_precomp_heq
    {P X Y H K : SSet.{u}} [Quasicategory P] [Quasicategory X]
    [Quasicategory Y] [Quasicategory H] [Quasicategory K]
    (p : P ⟶ X) (q : P ⟶ Y) (s : X ⟶ P) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful p)
    (hs : s ≫ p = 𝟙 X) (r : H ⟶ P) (t : K ⟶ H) (r' : K ⟶ P)
    (ht : t ≫ r = r') :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionTransportFactorIso p q s hp hs r).precomp t)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionTransportFactorIso p q s hp hs r') := by
  subst r'
  have he := homSpanSectionTransportFactorIso_heq p q s hp hs r
  have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_precomp_heq_of_heq _ _
    (by simp only [Category.assoc]) (by rw [Category.id_comp]) he t
  exact hh.trans ((heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp _ r t)).trans
    (homSpanSectionTransportFactorIso_heq p q s hp hs (t ≫ r)).symm)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
