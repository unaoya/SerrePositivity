module

public import SerrePositivity.KST.Comparison.PairHomotopyLifting
public import SerrePositivity.KST.Comparison.SubcomplexContraction

/-!
# 部分対象を保つ二段階の収縮の anodyne 性

概要：部分対象を保ち、その部分対象へ入る二段階の収縮から包含の anodyne 性を証明する。
方針：任意の Kan fibration に対し、部分対象上の値を指定して二つの区間写像を持ち上げる。
規約：Moss arXiv:1506.04887v2 §5 Theorem 5.1 への補助。
原典の strong anodyne な pairing とは異なり、相対ホモトピーから anodyne 性を示す。
使われ方：horn の逆像の局所化可逆性を anodyne 性へ強める。
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
概要：部分対象を保つ二段階の収縮を持つ包含は anodyne である。
方針：終点の部分対象への因子化から、相対的な区間の持ち上げを二回行う。
規約：原典の pairing による strong anodyne 性は主張しない。
使われ方：Kan fibration に沿う horn の逆像の包含。
-/
theorem subcomplex_inclusion_anodyne {X : SSet.{u}} (A : X.Subcomplex)
    (h₀ h₁ : X ⊗ (Δ[1] : SSet.{u}) ⟶ X)
    (h₀end : SSet.ι₁ ≫ h₀ = 𝟙 X) (hstart : SSet.ι₀ ≫ h₀ = SSet.ι₀ ≫ h₁)
    (h₀A : ∀ (d : SimplexCategoryᵒᵖ) (a : A.obj d) (t : (Δ[1] : SSet.{u}).obj d),
      h₀.app d (a.val, t) ∈ A.obj d)
    (h₁A : ∀ (d : SimplexCategoryᵒᵖ) (a : A.obj d) (t : (Δ[1] : SSet.{u}).obj d),
      h₁.app d (a.val, t) ∈ A.obj d)
    (hend : SSet.Subcomplex.range (SSet.ι₁ ≫ h₁) ≤ A) :
    SSet.anodyneExtensions A.ι := by
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
      ← Category.assoc, SSet.ι₀_comp, Category.assoc, Category.assoc, hstart]
  have he₁ : SSet.ι₁ ≫ v₁ = A.ι ≫ r := by
    apply (cancel_mono A.ι).mp
    rw [Category.assoc, hv₁, ← Category.assoc, SSet.ι₁_comp, Category.assoc]
    rfl
  have e₀ (Y : SSet.{u}) : intervalEndpoint Y 0 = SSet.ι₁ :=
    (AnodyneHomotopy.endpoint_one_factor Y).symm
  have e₁ (Y : SSet.{u}) : intervalEndpoint Y 1 = SSet.ι₀ :=
    (AnodyneHomotopy.endpoint_zero_factor Y).symm
  rw [SSet.anodyneExtensions_eq_llp_rlp]
  intro E B p hp
  constructor
  intro a b sq
  obtain ⟨l₁, _, hl₁A, hl₁p⟩ := relative_interval_lift A.ι p hp 0
    (r ≫ a) (v₁ ≫ a) (h₁ ≫ b)
    (by simp only [e₀, ← Category.assoc, he₁])
    (by rw [e₀, Category.assoc, sq.w]; rfl)
    (by rw [Category.assoc, sq.w, ← Category.assoc, hv₁, Category.assoc])
  obtain ⟨l₀, _, hl₀A, hl₀p⟩ := relative_interval_lift A.ι p hp 1
    (SSet.ι₀ ≫ l₁) (v₀ ≫ a) (h₀ ≫ b)
    (by rw [e₁, ← SSet.ι₀_comp_assoc, hl₁A, ← Category.assoc, ← hs, Category.assoc])
    (by rw [e₁, Category.assoc, hl₁p, ← Category.assoc, ← hstart, Category.assoc])
    (by rw [Category.assoc, sq.w, ← Category.assoc, hv₀, Category.assoc])
  refine ⟨⟨{ l := SSet.ι₁ ≫ l₀, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← SSet.ι₁_comp_assoc, hl₀A, ← Category.assoc, he₀, Category.id_comp]
  · rw [Category.assoc, hl₀p, ← Category.assoc, h₀end, Category.id_comp]

end SerrePositivity.KST.Comparison
