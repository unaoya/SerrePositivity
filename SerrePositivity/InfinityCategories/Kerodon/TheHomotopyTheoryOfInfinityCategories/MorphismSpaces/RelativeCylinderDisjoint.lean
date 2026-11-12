module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PushoutDisjoint

/-!
概要：固定部分を持つ写像円柱の残った端点の単射性の型での補題。
方針：固定部分の像を選択関数で延長し、二段の pushout 上に点を分離する関数を作る。
規約：元の射は固定部分の上でのみ単射性を要求する。
使われ方：Kerodon §4.6.2（Tag 01HM） の相対写像円柱。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：固定部分上で単射な射の相対写像円柱の残った端点は単射。
方針：各端点の点を some で区別する関数を二段の pushout に延長する。
規約：固定部分上での f∘i の単射性と二端点の相違を仮定する。
使われ方：Kerodon §4.6.2（Tag 01HM） の相対写像円柱の各次数での単射性。 -/
lemma relativeCylinder_endpoint_injective {A B C E R M : Type u}
    (i : A ⟶ B) (f : B ⟶ C) (k : B × E ⟶ R) (l : A ⟶ R)
    (r : R ⟶ M) (s : C ⟶ M) (e₀ e₁ : E) (he : e₁ ≠ e₀)
    (hR : IsPushout (↾fun a : A × E ↦ (i a.1, a.2)) (↾Prod.fst) k l)
    (hM : IsPushout (↾fun b ↦ k (b, e₀)) f r s)
    (hc : Function.Injective (fun a ↦ f (i a))) :
    Function.Injective (fun b ↦ r (k (b, e₁))) := by
  classical
  let v : C → Option B := Function.extend (fun a ↦ f (i a)) (fun a ↦ some (i a))
    (fun _ ↦ none)
  have hv (a : A) : v (f (i a)) = some (i a) := hc.extend_apply _ _ a
  let H : B × E → Option B := fun p ↦
    if p.2 = e₀ ∨ (∃ a, i a = p.1) then v (f p.1) else some p.1
  have hA (a : A) (t : E) : H (i a, t) = some (i a) := by
    dsimp only [H]
    rw [if_pos (Or.inr ⟨a, rfl⟩)]
    exact hv a
  have h₀ (b : B) : H (b, e₀) = v (f b) := by
    dsimp only [H]
    rw [if_pos (Or.inl rfl)]
  have h₁ (b : B) : H (b, e₁) = some b := by
    by_cases hb : ∃ a, i a = b
    · obtain ⟨a, rfl⟩ := hb
      exact hA a e₁
    · dsimp only [H]
      rw [if_neg (not_or.mpr ⟨he, hb⟩)]
  have hw : (↾fun a : A × E ↦ (i a.1, a.2)) ≫ (↾H) =
      (↾Prod.fst) ≫ (↾fun a ↦ some (i a)) := by
    apply ConcreteCategory.hom_ext
    intro a
    exact hA a.1 a.2
  obtain ⟨d, hk, _⟩ := hR.exists_desc (↾H) (↾fun a ↦ some (i a)) hw
  have hd : (↾fun b ↦ k (b, e₀)) ≫ d = f ≫ (↾v) := by
    apply ConcreteCategory.hom_ext
    intro b
    have hh := congrArg (fun z : (B × E) ⟶ Option B ↦ z (b, e₀)) hk
    exact hh.trans (h₀ b)
  obtain ⟨q, hq, _⟩ := hM.exists_desc d (↾v) hd
  have hq₁ (b : B) : q (r (k (b, e₁))) = some b := by
    have hh := ConcreteCategory.congr_hom hq (k (b, e₁))
    have hh' := congrArg (fun z : (B × E) ⟶ Option B ↦ z (b, e₁)) hk
    exact hh.trans (hh'.trans (h₁ b))
  intro b b' hbb
  have hh := congrArg (fun m ↦ q m) hbb
  rw [hq₁, hq₁] at hh
  exact Option.some.inj hh

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
