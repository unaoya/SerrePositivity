module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomSpanSectionTransport

/-!
概要：同じ共通 Hom 上で整合する三つの輸送は合成に関して関手同型を持つ。
方針：元の共通始域からの同値による前合成で比較し、充満忠実性で戻す。
規約：指定された三つの輸送作用そのものを比較する。
使われ方：元の可逆比較三角形から元の Hom 比較 span の合成則を取り出す。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 同じ共通始域からの前合成で一致する輸送の三角形は、大域的な関手同型で可換。 -/
def homTransportTriangleCoherence
    {H X₀ X₁ X₂ : SSet.{u}} [Quasicategory H] [Quasicategory X₀]
    [Quasicategory X₁] [Quasicategory X₂]
    (a : H ⟶ X₀) (b : H ⟶ X₁) (c : H ⟶ X₂)
    (t₀₁ : X₁ ⟶ X₀) (t₁₂ : X₂ ⟶ X₁) (t₀₂ : X₂ ⟶ X₀)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence c)
    (h₀₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (b ≫ t₀₁) a) (h₁₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (c ≫ t₁₂) b)
    (h₀₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (c ≫ t₀₂) a) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (t₁₂ ≫ t₀₁) t₀₂ := by
  apply (hc.precompose X₀).isFullyFaithful.preimageVertexIso
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (c ≫ (t₁₂ ≫ t₀₁)) (c ≫ t₀₂)
  have e := h₁₂.postcomp t₀₁ ≪≫ h₀₁ ≪≫ h₀₂.symm
  simpa only [Category.assoc] using e

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
