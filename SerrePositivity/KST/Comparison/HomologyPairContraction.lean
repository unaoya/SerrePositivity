module

public import SerrePositivity.KST.Comparison.HomologyHomotopy
public import SerrePositivity.KST.Comparison.HornPreimage

/-!
# 部分単体集合を保つ二段階収縮と整数ホモロジー

概要：部分単体集合へ入る二段階収縮から、包含の整数ホモロジー同型を構成する。
方針：両区間写像を部分単体集合へ制限し、端点の誘導射の一致で両逆を証明する。
規約：Waldhausen LNM 1126 §1.7・§1.8 のセル計算の準備。局所係数の主張とは区別する。
使われ方：horn 包含の整数ホモロジー比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory MonoidalCategory
open scoped Simplicial

/--
概要：任意の単体的区間写像の両端は同じ整数ホモロジー射を誘導する。
方針：区間写像そのものを両端の間の単体的ホモトピーとして使う。
規約：全自然数次数。
使われ方：二段階収縮のホモロジー計算。
-/
theorem integralHomologyMap_endpoints_eq {X Y : SSet.{u}}
    (h : X ⊗ (Δ[1] : SSet.{u}) ⟶ Y) (n : ℕ) :
    integralHomologyMap (SSet.ι₀ ≫ h) n = integralHomologyMap (SSet.ι₁ ≫ h) n := by
  let H : SSet.Homotopy (SSet.ι₀ ≫ h) (SSet.ι₁ ≫ h) := {
    h := h
    h₀ := rfl
    h₁ := rfl
    rel := by
      apply NatTrans.ext
      funext d
      apply ConcreteCategory.hom_ext
      intro x
      exact False.elim x.1.property }
  exact integralHomologyMap_eq_of_homotopy H n

/--
概要：部分単体集合を保つ二段階収縮を持つ包含は整数ホモロジー同型を誘導する。
方針：収縮の終点を逆写像とし、部分単体集合上と全体で両合成の誘導射を計算する。
規約：標準の二つの区間端点を使う。
使われ方：horn と標準単体の整数ホモロジー比較。
-/
def integralHomologyIsoOfPairContraction {X : SSet.{u}} (A : X.Subcomplex)
    (h₀ h₁ : X ⊗ (Δ[1] : SSet.{u}) ⟶ X)
    (h₀end : SSet.ι₁ ≫ h₀ = 𝟙 X) (hstart : SSet.ι₀ ≫ h₀ = SSet.ι₀ ≫ h₁)
    (h₀A : ∀ (d : SimplexCategoryᵒᵖ) (a : A.obj d) (t : (Δ[1] : SSet.{u}).obj d),
      h₀.app d (a.val, t) ∈ A.obj d)
    (h₁A : ∀ (d : SimplexCategoryᵒᵖ) (a : A.obj d) (t : (Δ[1] : SSet.{u}).obj d),
      h₁.app d (a.val, t) ∈ A.obj d)
    (hend : SSet.Subcomplex.range (SSet.ι₁ ≫ h₁) ≤ A) (n : ℕ) :
    integralHomology (A : SSet.{u}) n ≅ integralHomology X n := by
  let r := SSet.Subcomplex.lift (SSet.ι₁ ≫ h₁) hend
  let v₀ : (A : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ A :=
    SSet.Subcomplex.lift (A.ι ▷ (Δ[1] : SSet.{u}) ≫ h₀) (by
      rintro d x ⟨a, rfl⟩; exact h₀A d a.1 a.2)
  let v₁ : (A : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ A :=
    SSet.Subcomplex.lift (A.ι ▷ (Δ[1] : SSet.{u}) ≫ h₁) (by
      rintro d x ⟨a, rfl⟩; exact h₁A d a.1 a.2)
  have hv₀ : v₀ ≫ A.ι = A.ι ▷ (Δ[1] : SSet.{u}) ≫ h₀ := rfl
  have hv₁ : v₁ ≫ A.ι = A.ι ▷ (Δ[1] : SSet.{u}) ≫ h₁ := rfl
  have he₀ : SSet.ι₁ ≫ v₀ = 𝟙 (A : SSet.{u}) := by
    apply (cancel_mono A.ι).mp
    rw [Category.assoc, hv₀, ← Category.assoc, SSet.ι₁_comp,
      Category.assoc, h₀end, Category.comp_id, Category.id_comp]
  have hs : SSet.ι₀ ≫ v₀ = SSet.ι₀ ≫ v₁ := by
    apply (cancel_mono A.ι).mp
    rw [Category.assoc, hv₀, Category.assoc, hv₁, ← Category.assoc,
      ← Category.assoc, SSet.ι₀_comp,
      Category.assoc, Category.assoc, hstart]
  have he₁ : SSet.ι₁ ≫ v₁ = A.ι ≫ r := by
    apply (cancel_mono A.ι).mp
    rw [Category.assoc, hv₁, ← Category.assoc, SSet.ι₁_comp, Category.assoc]
    rfl
  refine {
    hom := integralHomologyMap A.ι n
    inv := integralHomologyMap r n
    hom_inv_id := ?_
    inv_hom_id := ?_ }
  · rw [← integralHomologyMap_comp, ← he₁, ← integralHomologyMap_endpoints_eq,
      ← hs, integralHomologyMap_endpoints_eq, he₀, integralHomologyMap_id]
  · rw [← integralHomologyMap_comp]
    change integralHomologyMap (SSet.ι₁ ≫ h₁) n = _
    rw [← integralHomologyMap_endpoints_eq, ← hstart,
      integralHomologyMap_endpoints_eq, h₀end, integralHomologyMap_id]

end SerrePositivity.KST.Comparison
