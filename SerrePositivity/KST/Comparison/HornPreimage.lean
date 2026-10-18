module

public import SerrePositivity.KST.Comparison.HornContraction
public import SerrePositivity.KST.Comparison.PairHomotopyLifting
public import SerrePositivity.KST.Comparison.SubcomplexContraction

/-!
# Kan fibration に沿う horn の逆像の局所化可逆性

概要：horn 包含の Kan fibration に沿う逆像は anodyne 局所化で同型となる。
方針：horn を保つ min(x,k) を経由する二つの収縮を持ち上げる。
規約：Segal 1974 Proposition 1.6 の対角模型の補助。Moss 2020 §5 Theorem 42 の
strong anodyne 性を引用せず、必要な局所化同型を実ホモトピーで証明する。
使われ方：ホモトピー引き戻しと骨格の貼り合わせを接続する。
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
概要：horn の添字にあたる頂点の定数単体は horn に含まれる。
方針：次元が正なら別の頂点 j があり、その頂点を定数単体は欠く。
規約：horn は正次元で扱う。零次元の空の horn には適用しない。
使われ方：収縮の終点が horn の逆像に入ること。
-/
theorem const_horn_vertex_mem {n : ℕ} [NeZero n] (k : Fin (n + 1))
    (d : SimplexCategoryᵒᵖ) (s : (Δ[n] : SSet.{u}).obj d) :
    (SSet.const (X := (Δ[n] : SSet.{u})) (SSet.stdSimplex.obj₀Equiv.symm k)).app d s ∈
      (Λ[n, k]).obj d := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have h01 : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at h'
    omega
  obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), j ≠ k := by
    by_cases h : k = 0
    · exact ⟨Fin.last n, fun h' => h01 ((h'.trans h).symm)⟩
    · exact ⟨0, Ne.symm h⟩
  rw [SSet.mem_horn_iff_notMem_range]
  refine ⟨j, hj, ?_⟩
  rintro ⟨i, hi⟩
  change k = j at hi
  exact hj hi.symm

/--
概要：Kan fibration に沿う正次元 horn の逆像の包含は局所化で可逆である。
方針：標準単体と horn の同時収縮を持ち上げ、逆像を保つ二つの区間写像を得る。
規約：Segal 1974 Proposition 1.6 の補助。strong anodyne 性を仮定も結論もしない。
使われ方：Kan fibration に沿う基底変換とセルの比較。
-/
theorem horn_preimage_localized_isIso {n : ℕ} [NeZero n] (k : Fin (n + 1))
    {E : SSet.{u}} (p : E ⟶ (Δ[n] : SSet.{u})) (hp : SSet.modelCategoryQuillen.J.rlp p) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((Λ[n, k]).preimage p).ι) := by
  let A := (Λ[n, k]).preimage p
  let H₀ := simplexMeetToIdentity.{u} k
  let H₁ := simplexMeetToVertex.{u} k
  have e₀ : intervalEndpoint E 0 = SSet.ι₁ := (AnodyneHomotopy.endpoint_one_factor E).symm
  have e₁ : intervalEndpoint E 1 = SSet.ι₀ := (AnodyneHomotopy.endpoint_zero_factor E).symm
  have hb₀ : (𝟙 E) ≫ p = intervalEndpoint E 0 ≫ (p ▷ (Δ[1] : SSet.{u}) ≫ H₀.h) := by
    rw [e₀, ← Category.assoc, SSet.ι₁_comp, Category.assoc, H₀.h₁,
      Category.comp_id, Category.id_comp]
  obtain ⟨h₀, h₀end, h₀base⟩ := interval_lift p hp 0 (𝟙 E)
    (p ▷ (Δ[1] : SSet.{u}) ≫ H₀.h) hb₀
  rw [e₀] at h₀end
  have hmeet : (SSet.ι₀ ≫ h₀) ≫ p = p ≫ simplexOrderMap (vertexMeet k) := by
    rw [Category.assoc, h₀base, ← Category.assoc, SSet.ι₀_comp, Category.assoc, H₀.h₀]
  have hb₁ : (SSet.ι₀ ≫ h₀) ≫ p = intervalEndpoint E 1 ≫
      (p ▷ (Δ[1] : SSet.{u}) ≫ H₁.h) := by
    calc
      _ = p ≫ simplexOrderMap (vertexMeet k) := hmeet
      _ = _ := by
        rw [e₁, ← Category.assoc, SSet.ι₀_comp, Category.assoc, H₁.h₀]
  obtain ⟨h₁, h₁start, h₁base⟩ := interval_lift p hp 1 (SSet.ι₀ ≫ h₀)
    (p ▷ (Δ[1] : SSet.{u}) ≫ H₁.h) hb₁
  rw [e₁] at h₁start
  have h₀A : ∀ (d : SimplexCategoryᵒᵖ) (a : A.obj d) (t : (Δ[1] : SSet.{u}).obj d),
      h₀.app d (a.val, t) ∈ A.obj d := by
    intro d a t
    change ((h₀ ≫ p).app d (a.val, t)) ∈ (Λ[n, k]).obj d
    rw [h₀base]
    exact simplexMeetToIdentity_mem_horn k d (p.app d a.val) a.property t
  have h₁A : ∀ (d : SimplexCategoryᵒᵖ) (a : A.obj d) (t : (Δ[1] : SSet.{u}).obj d),
      h₁.app d (a.val, t) ∈ A.obj d := by
    intro d a t
    change ((h₁ ≫ p).app d (a.val, t)) ∈ (Λ[n, k]).obj d
    rw [h₁base]
    exact simplexMeetToVertex_mem_horn k d (p.app d a.val) a.property t
  have hfinal : (SSet.ι₁ ≫ h₁) ≫ p = p ≫
      SSet.const (X := (Δ[n] : SSet.{u})) (SSet.stdSimplex.obj₀Equiv.symm k) := by
    rw [Category.assoc, h₁base, ← Category.assoc, SSet.ι₁_comp, Category.assoc, H₁.h₁]
  have hend : SSet.Subcomplex.range (SSet.ι₁ ≫ h₁) ≤ A := by
    rintro d x ⟨a, rfl⟩
    change ((SSet.ι₁ ≫ h₁) ≫ p).app d a ∈ (Λ[n, k]).obj d
    rw [hfinal]
    exact const_horn_vertex_mem k d (p.app d a)
  exact subcomplex_inclusion_localized_isIso A h₀ h₁ h₀end h₁start.symm h₀A h₁A hend

end SerrePositivity.KST.Comparison
