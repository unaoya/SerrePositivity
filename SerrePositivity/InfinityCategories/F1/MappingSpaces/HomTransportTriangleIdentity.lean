module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.HomTransportTriangleCoherence
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulFunctorIsoCoherence
public import SerrePositivity.InfinityCategories.F2.FunctorIsoWhiskerAlgebra

/-!
概要：既存の輸送三角形の同型を共通 Hom へ戻すと、指定された三辺の合成を回収する。
方針：前合成の充満忠実性による逆像の像を計算する。
規約：指定された三つの関手同型の値を保持する。
使われ方：元の分類 Hom の大域自然性と局所自然性の共有頂点三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 同値による前合成の同じ逆像は、元の指定関手同型を回収する。 -/
lemma IsQCatEquivalence.preimage_precompFunctorIso {H X Y : SSet.{u}}
    [Quasicategory H] [Quasicategory X] [Quasicategory Y]
    {c : H ⟶ X} (hc : IsQCatEquivalence c) {F G : X ⟶ Y}
    (e : FunctorIso (c ≫ F) (c ≫ G)) :
    FunctorIso.precomp ((hc.precompose Y).isFullyFaithful.preimageVertexIso e) c = e := by
  apply Iso.ext
  rw [F2.functorIso_precomp_hom]
  exact (hc.precompose Y).isFullyFaithful.toHoFullyFaithful.map_preimage
    (X := SSet.HomotopyCategory.mk (functorVertex F))
    (Y := SSet.HomotopyCategory.mk (functorVertex G)) e.hom

/-- 指定された三辺と輸送比較が同じ共通 Hom 上で満たす三角形の等式。 -/
def HomTransportTriangleCommutes
    {H X₀ X₁ X₂ : SSet.{u}}
    (a : H ⟶ X₀) (b : H ⟶ X₁) (c : H ⟶ X₂)
    (t₀₁ : X₁ ⟶ X₀) (t₁₂ : X₂ ⟶ X₁) (t₀₂ : X₂ ⟶ X₀)
    (h₀₁ : FunctorIso (b ≫ t₀₁) a) (h₁₂ : FunctorIso (c ≫ t₁₂) b)
    (h₀₂ : FunctorIso (c ≫ t₀₂) a) (e : FunctorIso (t₁₂ ≫ t₀₁) t₀₂) : Prop :=
  e.precomp c ≪≫ h₀₂ = h₁₂.postcomp t₀₁ ≪≫ h₀₁

/-- 既存の輸送三角形は、同じ共通 Hom 上で指定された二辺の合成そのものを回収する。 -/
lemma homTransportTriangleCoherence_identity
    {H X₀ X₁ X₂ : SSet.{u}} [Quasicategory H] [Quasicategory X₀]
    [Quasicategory X₁] [Quasicategory X₂]
    (a : H ⟶ X₀) (b : H ⟶ X₁) (c : H ⟶ X₂)
    (t₀₁ : X₁ ⟶ X₀) (t₁₂ : X₂ ⟶ X₁) (t₀₂ : X₂ ⟶ X₀)
    (hc : IsQCatEquivalence c)
    (h₀₁ : FunctorIso (b ≫ t₀₁) a) (h₁₂ : FunctorIso (c ≫ t₁₂) b)
    (h₀₂ : FunctorIso (c ≫ t₀₂) a) :
    (homTransportTriangleCoherence a b c t₀₁ t₁₂ t₀₂ hc h₀₁ h₁₂ h₀₂).precomp c ≪≫ h₀₂ =
      h₁₂.postcomp t₀₁ ≪≫ h₀₁ := by
  have h := hc.preimage_precompFunctorIso
    (show FunctorIso (c ≫ (t₁₂ ≫ t₀₁)) (c ≫ t₀₂) from
      h₁₂.postcomp t₀₁ ≪≫ h₀₁ ≪≫ h₀₂.symm)
  change (homTransportTriangleCoherence a b c t₀₁ t₁₂ t₀₂ hc h₀₁ h₁₂ h₀₂).precomp c = _ at h
  rw [h]
  simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

end SerrePositivity.InfinityCategories
