module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.ChainGluing

/-!
概要：整合する全前置段の延長から、一つの全整合段族を well-founded 再帰で選ぶ。
方針：未整合な再帰入力には none を返し、帰納法で実際の全段が整合して存在することを示す。
規約：前置整合性や全段の存在を公理として追加しない。
使われ方：相対交互構成の後続段と極限段の選択を一つの塔にまとめる。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：整合する全過去段を延長できれば、整合する全段族が存在する。
方針：Option 値の well-founded 再帰を作り、帰納法で全段の存在と厳密な延長を同時に示す。
規約：段型に既定値を要求せず、延長関係を同型へ弱めない。
使われ方：各前置段の全単体を保持する長さ κ₀ の相対交互塔。 -/
lemma exists_wellFounded_coherentChoice {I : Type u} [LT I]
    (wf : WellFounded ((· < ·) : I → I → Prop)) (S : I → Type v)
    (R : ∀ {a b : I}, S a → S b → Prop)
    (extend : ∀ a (prev : ∀ b, b < a → S b),
      (∀ b c (hb : b < a) (hc : c < a), b < c → R (prev b hb) (prev c hc)) →
      ∃ s : S a, ∀ b (hb : b < a), R (prev b hb) s) :
    ∃ s : ∀ a, S a, ∀ a b, a < b → R (s a) (s b) := by
  classical
  let step (a : I) (prev : ∀ b, b < a → Option (S b)) : Option (S a) :=
    if h : ∀ b (hb : b < a), ∃ s, prev b hb = some s then
      let p := fun b hb ↦ Classical.choose (h b hb)
      if hc : ∀ b c (hb : b < a) (hc : c < a), b < c → R (p b hb) (p c hc) then
        some (Classical.choose (extend a p hc))
      else none
    else none
  let go := wf.fix step
  have hgo (a : I) : go a = step a (fun b _ ↦ go b) := wf.fix_eq step a
  have hall : ∀ a, ∃ s : S a, go a = some s ∧
      ∀ b, b < a → ∀ t : S b, go b = some t → R t s := by
    intro a
    induction a using wf.induction with
    | h a ih =>
      have hp : ∀ b (hb : b < a), ∃ s, go b = some s := by
        intro b hb
        obtain ⟨s, hs, _⟩ := ih b hb
        exact ⟨s, hs⟩
      let p := fun b hb ↦ Classical.choose (hp b hb)
      have hpc : ∀ b c (hb : b < a) (hc : c < a), b < c → R (p b hb) (p c hc) := by
        intro b c hb hc hbc
        obtain ⟨s, hs, hR⟩ := ih c hc
        have hs' : s = p c hc := Option.some.inj (hs.symm.trans (Classical.choose_spec (hp c hc)))
        exact hs' ▸ hR b hbc (p b hb) (Classical.choose_spec (hp b hb))
      let s := Classical.choose (extend a p hpc)
      have hs : go a = some s := by
        rw [hgo]
        dsimp only [step]
        rw [dif_pos hp, dif_pos hpc]
      refine ⟨s, hs, ?_⟩
      intro b hb t ht
      have ht' : t = p b hb := Option.some.inj (ht.symm.trans (Classical.choose_spec (hp b hb)))
      exact ht'.symm ▸ Classical.choose_spec (extend a p hpc) b hb
  refine ⟨fun a ↦ Classical.choose (hall a), ?_⟩
  intro a b hab
  exact (Classical.choose_spec (hall b)).2 a hab (Classical.choose (hall a))
    (Classical.choose_spec (hall a)).1

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
