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
概要：番号零の区間端点は一端点である。
方針：点との積の同型による端点の表示を使う。
規約：番号は除く頂点を表す。
使われ方：向きを指定した収縮の標準端点への変換。
-/
@[simp] theorem intervalEndpoint_zero_eq (X : SSet.{u}) : intervalEndpoint X 0 = SSet.ι₁ :=
  (AnodyneHomotopy.endpoint_one_factor X).symm

/--
概要：番号一の区間端点は零端点である。
方針：点との積の同型による端点の表示を使う。
規約：番号は除く頂点を表す。
使われ方：向きを指定した収縮の標準端点への変換。
-/
@[simp] theorem intervalEndpoint_one_eq (X : SSet.{u}) : intervalEndpoint X 1 = SSet.ι₀ :=
  (AnodyneHomotopy.endpoint_zero_factor X).symm

/--
概要：番号で指定した区間端点は単体的写像と可換である。
方針：二つの端点の場合に分け、標準端点の自然性を使う。
規約：番号 1 は零端点、番号 0 は一端点。
使われ方：任意の向きの相対収縮の持ち上げ。
-/
@[reassoc] theorem intervalEndpoint_naturality {A X : SSet.{u}} (f : A ⟶ X) (ε : Fin 2) :
    intervalEndpoint A ε ≫ f ▷ Δ[1] = f ≫ intervalEndpoint X ε := by
  fin_cases ε
  · change intervalEndpoint A 0 ≫ f ▷ Δ[1] = f ≫ intervalEndpoint X 0
    rw [intervalEndpoint_zero_eq, intervalEndpoint_zero_eq]
    exact SSet.ι₁_comp f
  · change intervalEndpoint A 1 ≫ f ▷ Δ[1] = f ≫ intervalEndpoint X 1
    rw [intervalEndpoint_one_eq, intervalEndpoint_one_eq]
    exact SSet.ι₀_comp f

/--
概要：部分対象を保つ二段階の収縮を持つ包含は anodyne である。
方針：終点の部分対象への因子化から、相対的な区間の持ち上げを二回行う。
規約：原典の pairing による strong anodyne 性は主張しない。
使われ方：Kan fibration に沿う horn の逆像の包含。
-/
theorem subcomplex_pairContraction_anodyne {X : SSet.{u}} (A : X.Subcomplex)
    (ε₀ ε₁ : Fin 2)
    (h₀ h₁ : X ⊗ (Δ[1] : SSet.{u}) ⟶ X)
    (h₀end : intervalEndpoint X ε₀ ≫ h₀ = 𝟙 X)
    (hstart : intervalEndpoint X ε₀.rev ≫ h₀ = intervalEndpoint X ε₁ ≫ h₁)
    (h₀A : ∀ (d : SimplexCategoryᵒᵖ) (a : A.obj d) (t : (Δ[1] : SSet.{u}).obj d),
      h₀.app d (a.val, t) ∈ A.obj d)
    (h₁A : ∀ (d : SimplexCategoryᵒᵖ) (a : A.obj d) (t : (Δ[1] : SSet.{u}).obj d),
      h₁.app d (a.val, t) ∈ A.obj d)
    (hend : SSet.Subcomplex.range (intervalEndpoint X ε₁.rev ≫ h₁) ≤ A) :
    SSet.anodyneExtensions A.ι := by
  let r := SSet.Subcomplex.lift (intervalEndpoint X ε₁.rev ≫ h₁) hend
  let v₀ : (A : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ A :=
    SSet.Subcomplex.lift (A.ι ▷ (Δ[1] : SSet.{u}) ≫ h₀) (by
      rintro d x ⟨a, rfl⟩; exact h₀A d a.1 a.2)
  let v₁ : (A : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ A :=
    SSet.Subcomplex.lift (A.ι ▷ (Δ[1] : SSet.{u}) ≫ h₁) (by
      rintro d x ⟨a, rfl⟩; exact h₁A d a.1 a.2)
  have hv₀ : v₀ ≫ A.ι = A.ι ▷ (Δ[1] : SSet.{u}) ≫ h₀ := rfl
  have hv₁ : v₁ ≫ A.ι = A.ι ▷ (Δ[1] : SSet.{u}) ≫ h₁ := rfl
  have he₀ : intervalEndpoint (A : SSet.{u}) ε₀ ≫ v₀ = 𝟙 (A : SSet.{u}) := by
    apply (cancel_mono A.ι).mp
    rw [Category.assoc, hv₀, ← Category.assoc, intervalEndpoint_naturality,
      Category.assoc, h₀end, Category.comp_id, Category.id_comp]
  have hs : intervalEndpoint (A : SSet.{u}) ε₀.rev ≫ v₀ =
      intervalEndpoint (A : SSet.{u}) ε₁ ≫ v₁ := by
    apply (cancel_mono A.ι).mp
    rw [Category.assoc, hv₀, Category.assoc, hv₁, ← Category.assoc,
      ← Category.assoc, intervalEndpoint_naturality, intervalEndpoint_naturality,
      Category.assoc, Category.assoc, hstart]
  have he₁ : intervalEndpoint (A : SSet.{u}) ε₁.rev ≫ v₁ = A.ι ≫ r := by
    apply (cancel_mono A.ι).mp
    rw [Category.assoc, hv₁, ← Category.assoc, intervalEndpoint_naturality, Category.assoc]
    rfl
  rw [SSet.anodyneExtensions_eq_llp_rlp]
  intro E B p hp
  constructor
  intro a b sq
  obtain ⟨l₁, _, hl₁A, hl₁p⟩ := relative_interval_lift A.ι p hp ε₁.rev
    (r ≫ a) (v₁ ≫ a) (h₁ ≫ b)
    (by simp only [← Category.assoc, he₁])
    (by rw [Category.assoc, sq.w]; rfl)
    (by rw [Category.assoc, sq.w, ← Category.assoc, hv₁, Category.assoc])
  obtain ⟨l₀, _, hl₀A, hl₀p⟩ := relative_interval_lift A.ι p hp ε₀.rev
    (intervalEndpoint X ε₁ ≫ l₁) (v₀ ≫ a) (h₀ ≫ b)
    (by rw [← intervalEndpoint_naturality_assoc, hl₁A, ← Category.assoc, ← hs, Category.assoc])
    (by rw [Category.assoc, hl₁p, ← Category.assoc, ← hstart, Category.assoc])
    (by rw [Category.assoc, sq.w, ← Category.assoc, hv₀, Category.assoc])
  refine ⟨⟨{ l := intervalEndpoint X ε₀ ≫ l₀, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← intervalEndpoint_naturality_assoc, hl₀A, ← Category.assoc, he₀, Category.id_comp]
  · rw [Category.assoc, hl₀p, ← Category.assoc, h₀end, Category.id_comp]

/--
概要：共通の始点を持つ二段階の収縮から、部分単体集合の包含の anodyne 性を得る。
方針：向きを指定できる収縮の補題を、零端点を共有する場合へ適用する。
規約：horn の逆像の min(x,k) を経由する二つの収縮。
使われ方：既存の horn の逆像の証明の界面。
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
  apply subcomplex_pairContraction_anodyne A 0 1 h₀ h₁
  · simpa only [intervalEndpoint_zero_eq] using h₀end
  · simpa only [show (0 : Fin 2).rev = 1 by decide,
      intervalEndpoint_one_eq] using hstart
  · exact h₀A
  · exact h₁A
  · simpa only [show (1 : Fin 2).rev = 0 by decide,
      intervalEndpoint_zero_eq] using hend

end SerrePositivity.KST.Comparison
