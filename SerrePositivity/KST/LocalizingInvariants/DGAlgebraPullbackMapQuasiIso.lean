module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPullbackMap

/-!
概要：左脚が次数全射な実 cospan 間の成分準同型は、元の厳密 pullback でも準同型になる。
方針：元の経路模型への準同型比較とその自然性を介して反映する。
規約：元の比較射を使い、一般の ∞ 普遍性を入力しない。使われ方：相対拡大の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PullbackMap
variable (R : Type u) [CommRing R] {A₀ B₀ C₀ A₁ B₁ C₁ : Mon (Complex R)}
  (f₀ : A₀ ⟶ B₀) (g₀ : C₀ ⟶ B₀) (f₁ : A₁ ⟶ B₁) (g₁ : C₁ ⟶ B₁)
  (a : A₀ ⟶ A₁) (b : B₀ ⟶ B₁) (c : C₀ ⟶ C₁)
  (hf : a ≫ f₁ = f₀ ≫ b) (hg : c ≫ g₁ = g₀ ≫ b)

lemma map_quasiIso [Epi f₀.hom] [Epi f₁.hom]
    (ha : QuasiIso a.hom) (hb : QuasiIso b.hom) (hc : QuasiIso c.hom) :
    QuasiIso (map R f₀ g₀ f₁ g₁ a b c hf hg).hom := by
  have h₀ := HomotopyPullbackModel.comparison_quasiIso_left R f₀ g₀
  have h₁ := HomotopyPullbackModel.comparison_quasiIso_left R f₁ g₁
  have hm := HomotopyPullbackModel.map_quasiIso R f₀ g₀ f₁ g₁ a b c hf hg ha hb hc
  have hh : QuasiIso ((map R f₀ g₀ f₁ g₁ a b c hf hg).hom ≫
      (HomotopyPullbackModel.comparison R f₁ g₁).hom) := by
    change QuasiIso ((map R f₀ g₀ f₁ g₁ a b c hf hg ≫
      HomotopyPullbackModel.comparison R f₁ g₁).hom)
    rw [← comparison_naturality]
    exact quasiIso_comp _ _ (hφ := h₀) (hφ' := hm)
  exact quasiIso_of_comp_right (map R f₀ g₀ f₁ g₁ a b c hf hg).hom
    (HomotopyPullbackModel.comparison R f₁ g₁).hom

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PullbackMap
