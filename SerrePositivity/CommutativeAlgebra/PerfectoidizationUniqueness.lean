module

public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid

/-! # 普遍 perfectoid 化の選択に依存しない比較

同じ環の二つの普遍 perfectoid 化は、元環からの写像と両立する同型を持つ。
標準写像の全射性もこの同型を通して移る。全射性自体を普遍性からは導かない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity

namespace IsPerfectoidization

/-- 二つの普遍 perfectoid 化を結ぶ、元環からの写像と両立する同型。 -/
theorem exists_equiv {S C D : Type u} [CommRing S] [CommRing C] [CommRing D]
    (p : ℕ) [Fact p.Prime] {f : S →+* C} {g : S →+* D}
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g) :
    ∃ e : C ≃+* D, e.toRingHom.comp f = g := by
  obtain ⟨a, ha, hua⟩ := hf.2 D hg.1 g
  obtain ⟨b, hb, hub⟩ := hg.2 C hf.1 f
  have hba : b.comp a = RingHom.id C := by
    obtain ⟨l, hl, hul⟩ := hf.2 C hf.1 f
    exact (hul _ (by change (b.comp a).comp f = f; rw [RingHom.comp_assoc, ha, hb])).trans
      (hul _ (RingHom.id_comp f)).symm
  have hab : a.comp b = RingHom.id D := by
    obtain ⟨l, hl, hul⟩ := hg.2 D hg.1 g
    exact (hul _ (by change (a.comp b).comp g = g; rw [RingHom.comp_assoc, hb, ha])).trans
      (hul _ (RingHom.id_comp g)).symm
  exact ⟨{ a with invFun := b
                  left_inv := fun x ↦ DFunLike.congr_fun hba x
                  right_inv := fun x ↦ DFunLike.congr_fun hab x }, ha⟩

/-- 普遍対象のモデルを変えても、元環からの標準写像の全射性は変わらない。 -/
theorem surjective_iff {S C D : Type u} [CommRing S] [CommRing C] [CommRing D]
    (p : ℕ) [Fact p.Prime] {f : S →+* C} {g : S →+* D}
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g) :
    Function.Surjective f ↔ Function.Surjective g := by
  obtain ⟨e, he⟩ := hf.exists_equiv p hg
  constructor
  · intro h
    rw [← he]
    exact e.surjective.comp h
  · intro h x
    obtain ⟨s, hs⟩ := h (e x)
    refine ⟨s, e.injective ?_⟩
    exact (DFunLike.congr_fun he s).trans hs

/-- 元環で定義される核イデアルも、普遍perfectoid化のモデルに依存しない。 -/
theorem ker_eq {S C D : Type u} [CommRing S] [CommRing C] [CommRing D]
    (p : ℕ) [Fact p.Prime] {f : S →+* C} {g : S →+* D}
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g) :
    RingHom.ker f = RingHom.ker g := by
  obtain ⟨e, he⟩ := hf.exists_equiv p hg
  ext x
  change f x = 0 ↔ g x = 0
  have hx : e (f x) = g x := DFunLike.congr_fun he x
  constructor
  · intro h
    rw [← hx, h, map_zero]
  · intro h
    apply e.injective
    rw [hx, h, map_zero]

end IsPerfectoidization
end SerrePositivity
