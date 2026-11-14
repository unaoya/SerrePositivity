module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.JointRealizationComposition

/-!
概要：指定図式同型の端点正規化は逆同型と三因子の合成を保つ。
方針：元の端点等式を消去し、既存の二因子の合成則を使う。
規約：指定同型の値を保持する。
使われ方：Kerodon §5.6（Tag 027M）の指定底変換の貼り合わせの中間同型の相殺。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories
namespace PresentableInfinityCategories

/-- 概要：同じ端点正規化と逆同型は交換する。
方針：端点等式を消去する。規約：同じ逆同型。
使われ方：切断比較の逆と指定分類底変換の因子を照合する。 -/
lemma diagramIsoCongr_symm {A X : SSet.{u}} {f g f' g' : A ⟶ X}
    (hf : f = f') (hg : g = g') (e : FunctorIso f g) :
    diagramIsoCongr hg hf e.symm = (diagramIsoCongr hf hg e).symm := by
  subst f' g'
  simp only [diagramIsoCongr, eqToIso_refl, Iso.refl_symm, Iso.refl_trans,
    Iso.trans_refl]

/-- 概要：同じ四端点による正規化は同じ三因子の合成を保つ。
方針：既存の二因子の合成則を二回使う。
規約：中間端点の等式を共用する。使われ方：係数での貼り合わせを同じ端点へ移す。 -/
lemma diagramIsoCongr_trans_three {A X : SSet.{u}}
    {f₀ f₁ f₂ f₃ g₀ g₁ g₂ g₃ : A ⟶ X}
    (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) (h₂ : f₂ = g₂) (h₃ : f₃ = g₃)
    (e₁ : FunctorIso f₀ f₁) (e₂ : FunctorIso f₁ f₂) (e₃ : FunctorIso f₂ f₃) :
    diagramIsoCongr h₀ h₃ (e₁ ≪≫ e₂ ≪≫ e₃) =
      diagramIsoCongr h₀ h₁ e₁ ≪≫ diagramIsoCongr h₁ h₂ e₂ ≪≫ diagramIsoCongr h₂ h₃ e₃ := by
  rw [diagramIsoCongr_trans h₀ h₁ h₃, diagramIsoCongr_trans h₁ h₂ h₃]


/-- 概要：同じ指定同型の二表示は同じ両端点への正規化後に一致する。
方針：二つの正規化の異種等式を合成する。規約：同じ指定値。
使われ方：係数貼り合わせの各因子を元の係数底変換へ戻す。 -/
lemma diagramIsoCongr_eq_of_heq {A X : SSet.{u}}
    {f g f' g' h k : A ⟶ X} (hf : f = h) (hg : g = k)
    (hf' : f' = h) (hg' : g' = k)
    (e : FunctorIso f g) (e' : FunctorIso f' g') (he : HEq e e') :
    diagramIsoCongr hf hg e = diagramIsoCongr hf' hg' e' := by
  exact eq_of_heq ((diagramIsoCongr_heq hf hg e).trans
    (he.trans (diagramIsoCongr_heq hf' hg' e').symm))

end PresentableInfinityCategories
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories
