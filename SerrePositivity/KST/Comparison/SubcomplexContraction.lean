module

public import SerrePositivity.KST.Comparison.FiberwiseAnodyne
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-!
# 部分単体集合を保つ二段階の収縮

概要：部分対象へ入る収縮の zigzag から、その包含の局所化可逆性を証明する。
方針：全空間と部分対象の双方で区間の端点の像を等置する。
規約：Segal 1974 Proposition 1.6 の引き戻し比較の補助。収縮は厳密な単体的写像で与える。
使われ方：Kan fibration に沿って持ち上げた horn の収縮に適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
open SerrePositivity.SimplicialModel

/--
概要：局所化関手は任意の区間写像の二つの端点を等しくする。
方針：anodyne な区間端点の像の一致に写像を後合成する。
規約：Segal 1974 Proposition 1.6 の実ホモトピーの規約。
使われ方：端点の式で指定された収縮を直接扱う。
-/
theorem localized_interval_endpoints {X Y : SSet.{u}} (h : X ⊗ (Δ[1] : SSet.{u}) ⟶ Y) :
    AnodyneHomotopy.anodyneQ.map (SSet.ι₀ ≫ h) =
      AnodyneHomotopy.anodyneQ.map (SSet.ι₁ ≫ h) := by
  rw [Functor.map_comp, Functor.map_comp,
    AnodyneHomotopy.endpoint_images_eq AnodyneHomotopy.anodyneQ
      (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)]

/--
概要：部分対象を保ち、その部分対象へ入る二段階の収縮は包含を局所化同型にする。
方針：二つの区間写像を部分対象にも制限し、終点の因子化から両側逆を作る。
規約：Segal 1974 Proposition 1.6 の補助。片方の収縮を逆向きに辿る zigzag を使う。
使われ方：horn の逆像と全空間の比較。
-/
theorem subcomplex_inclusion_localized_isIso {X : SSet.{u}} (A : X.Subcomplex)
    (h₀ h₁ : X ⊗ (Δ[1] : SSet.{u}) ⟶ X)
    (h₀end : SSet.ι₁ ≫ h₀ = 𝟙 X) (hstart : SSet.ι₀ ≫ h₀ = SSet.ι₀ ≫ h₁)
    (h₀A : ∀ (d : SimplexCategoryᵒᵖ) (a : A.obj d) (t : (Δ[1] : SSet.{u}).obj d),
      h₀.app d (a.val, t) ∈ A.obj d)
    (h₁A : ∀ (d : SimplexCategoryᵒᵖ) (a : A.obj d) (t : (Δ[1] : SSet.{u}).obj d),
      h₁.app d (a.val, t) ∈ A.obj d)
    (hend : SSet.Subcomplex.range (SSet.ι₁ ≫ h₁) ≤ A) :
    IsIso (AnodyneHomotopy.anodyneQ.map A.ι) := by
  let r := SSet.Subcomplex.lift (SSet.ι₁ ≫ h₁) hend
  let v₀ : (A : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ A :=
    SSet.Subcomplex.lift (A.ι ▷ (Δ[1] : SSet.{u}) ≫ h₀) (by
      rintro d x ⟨a, rfl⟩
      exact h₀A d a.1 a.2)
  let v₁ : (A : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ A :=
    SSet.Subcomplex.lift (A.ι ▷ (Δ[1] : SSet.{u}) ≫ h₁) (by
      rintro d x ⟨a, rfl⟩
      exact h₁A d a.1 a.2)
  have hv₀ : v₀ ≫ A.ι = A.ι ▷ (Δ[1] : SSet.{u}) ≫ h₀ := rfl
  have hv₁ : v₁ ≫ A.ι = A.ι ▷ (Δ[1] : SSet.{u}) ≫ h₁ := rfl
  have he₀ : SSet.ι₁ ≫ v₀ = 𝟙 (A : SSet.{u}) := by
    apply (cancel_mono A.ι).mp
    rw [Category.assoc, hv₀, ← Category.assoc, SSet.ι₁_comp,
      Category.assoc, h₀end, Category.comp_id, Category.id_comp]
  have hs : SSet.ι₀ ≫ v₀ = SSet.ι₀ ≫ v₁ := by
    apply (cancel_mono A.ι).mp
    rw [Category.assoc, hv₀, Category.assoc, hv₁, ← Category.assoc,
      ← Category.assoc, SSet.ι₀_comp, Category.assoc, Category.assoc, hstart]
  have he₁ : SSet.ι₁ ≫ v₁ = A.ι ≫ r := by
    apply (cancel_mono A.ι).mp
    rw [Category.assoc, hv₁, ← Category.assoc, SSet.ι₁_comp, Category.assoc]
    rfl
  let Q := AnodyneHomotopy.anodyneQ
  have hri : Q.map (r ≫ A.ι) = 𝟙 (Q.obj X) := by
    change Q.map (SSet.ι₁ ≫ h₁) = _
    rw [← localized_interval_endpoints h₁, ← hstart, localized_interval_endpoints h₀,
      h₀end, Q.map_id]
  have hir : Q.map (A.ι ≫ r) = 𝟙 (Q.obj (A : SSet.{u})) := by
    rw [← he₁, ← localized_interval_endpoints v₁, ← hs, localized_interval_endpoints v₀,
      he₀, Q.map_id]
  exact (show Q.obj (A : SSet.{u}) ≅ Q.obj X from
    { hom := Q.map A.ι
      inv := Q.map r
      hom_inv_id := (Q.map_comp _ _).symm.trans hir
      inv_hom_id := (Q.map_comp _ _).symm.trans hri }).isIso_hom

end SerrePositivity.KST.Comparison
