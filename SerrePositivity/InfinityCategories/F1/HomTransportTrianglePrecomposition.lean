module

public import SerrePositivity.InfinityCategories.F1.HomTransportTriangleIdentity
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoWhiskerCancellation

/-!
概要：指定輸送三角形の等式を同じ共通 Hom へ写る任意の作用で引き戻す。
方針：同型の前合成の合成則と前後合成の交換を使う。
規約：元の三辺と指定結合同型の値を保持する。
使われ方：共有頂点での同じ元の大域 Hom 作用の整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 指定三角形の等式は、同じ共通 Hom からの任意の作用で引き戻しても成立する。 -/
lemma HomTransportTriangleCommutes.precomp
    {H X₀ X₁ X₂ K : SSet.{u}}
    (a : H ⟶ X₀) (b : H ⟶ X₁) (c : H ⟶ X₂)
    (t₀₁ : X₁ ⟶ X₀) (t₁₂ : X₂ ⟶ X₁) (t₀₂ : X₂ ⟶ X₀)
    (h₀₁ : FunctorIso (b ≫ t₀₁) a) (h₁₂ : FunctorIso (c ≫ t₁₂) b)
    (h₀₂ : FunctorIso (c ≫ t₀₂) a) (e : FunctorIso (t₁₂ ≫ t₀₁) t₀₂)
    (h : HomTransportTriangleCommutes a b c t₀₁ t₁₂ t₀₂ h₀₁ h₁₂ h₀₂ e)
    (r : K ⟶ H) :
    HomTransportTriangleCommutes (r ≫ a) (r ≫ b) (r ≫ c) t₀₁ t₁₂ t₀₂
      (h₀₁.precomp r) (h₁₂.precomp r) (h₀₂.precomp r) e := by
  unfold HomTransportTriangleCommutes at h ⊢
  have hh := congrArg (fun v ↦ FunctorIso.precomp v r) h
  simpa only [F2.functorIso_precomp_trans, F2.functorIso_precomp_precomp,
    ← F2.functorIso_precomp_postcomp] using hh

/-- 元の三辺の指定同型を同じ作用で前合成して得る三角形の貼り合わせ等式。 -/
def HomTransportTriangleCommutesAt
    {H X₀ X₁ X₂ K : SSet.{u}}
    (a : H ⟶ X₀) (b : H ⟶ X₁) (c : H ⟶ X₂)
    (t₀₁ : X₁ ⟶ X₀) (t₁₂ : X₂ ⟶ X₁) (t₀₂ : X₂ ⟶ X₀)
    (h₀₁ : FunctorIso (b ≫ t₀₁) a) (h₁₂ : FunctorIso (c ≫ t₁₂) b)
    (h₀₂ : FunctorIso (c ≫ t₀₂) a) (e : FunctorIso (t₁₂ ≫ t₀₁) t₀₂)
    (r : K ⟶ H) : Prop :=
  (e.precomp c).precomp r ≪≫ h₀₂.precomp r =
    (h₁₂.postcomp t₀₁).precomp r ≪≫ h₀₁.precomp r

/-- 指定三角形の貼り合わせ等式に、同じ元の前合成作用を施す。 -/
lemma HomTransportTriangleCommutes.at_map
    {H X₀ X₁ X₂ K : SSet.{u}}
    (a : H ⟶ X₀) (b : H ⟶ X₁) (c : H ⟶ X₂)
    (t₀₁ : X₁ ⟶ X₀) (t₁₂ : X₂ ⟶ X₁) (t₀₂ : X₂ ⟶ X₀)
    (h₀₁ : FunctorIso (b ≫ t₀₁) a) (h₁₂ : FunctorIso (c ≫ t₁₂) b)
    (h₀₂ : FunctorIso (c ≫ t₀₂) a) (e : FunctorIso (t₁₂ ≫ t₀₁) t₀₂)
    (h : HomTransportTriangleCommutes a b c t₀₁ t₁₂ t₀₂ h₀₁ h₁₂ h₀₂ e)
    (r : K ⟶ H) :
    HomTransportTriangleCommutesAt a b c t₀₁ t₁₂ t₀₂ h₀₁ h₁₂ h₀₂ e r := by
  unfold HomTransportTriangleCommutes at h
  unfold HomTransportTriangleCommutesAt
  have hh := congrArg (fun v ↦ FunctorIso.precomp v r) h
  simpa only [F2.functorIso_precomp_trans] using hh

/-- 前合成してから貼る表示は、元の合成した作用による三角形の表示と同値。 -/
lemma homTransportTriangleCommutesAt_iff
    {H X₀ X₁ X₂ K : SSet.{u}}
    (a : H ⟶ X₀) (b : H ⟶ X₁) (c : H ⟶ X₂)
    (t₀₁ : X₁ ⟶ X₀) (t₁₂ : X₂ ⟶ X₁) (t₀₂ : X₂ ⟶ X₀)
    (h₀₁ : FunctorIso (b ≫ t₀₁) a) (h₁₂ : FunctorIso (c ≫ t₁₂) b)
    (h₀₂ : FunctorIso (c ≫ t₀₂) a) (e : FunctorIso (t₁₂ ≫ t₀₁) t₀₂) (r : K ⟶ H) :
    HomTransportTriangleCommutesAt a b c t₀₁ t₁₂ t₀₂ h₀₁ h₁₂ h₀₂ e r ↔
      HomTransportTriangleCommutes (r ≫ a) (r ≫ b) (r ≫ c) t₀₁ t₁₂ t₀₂
        (h₀₁.precomp r) (h₁₂.precomp r) (h₀₂.precomp r) e := by
  simp only [HomTransportTriangleCommutesAt, HomTransportTriangleCommutes,
    F2.functorIso_precomp_precomp, ← F2.functorIso_precomp_postcomp]

end SerrePositivity.InfinityCategories
