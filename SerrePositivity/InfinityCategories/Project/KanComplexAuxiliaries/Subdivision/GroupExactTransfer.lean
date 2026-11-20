module


public import Mathlib.Algebra.Group.Equiv.Basic

/-!
概要：可換な群同型による核と像の完全性の移送。
方針：三つの同型の単射・全射と単位保存を使う。
規約：群の可換性は仮定しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。段の完全列から整数次数への移送。
-/

@[expose] public section

universe u

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra

/-- 概要：群同型で可換に対応する二つの射の完全性を移す。
方針：核の元を同型で送り、像の原像を逆同型で戻す。
規約：完全性は単位の逆像と前の射の像の一致として述べる。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。整数次数の長完全列。 -/
theorem group_exact_of_equivalences {A B C A' B' C' : Type u}
    [Group A] [Group B] [Group C] [Group A'] [Group B'] [Group C']
    (f : A →* B) (g : B →* C) (f' : A' →* B') (g' : B' →* C')
    (eA : A ≃* A') (eB : B ≃* B') (eC : C ≃* C')
    (hF : ∀ a, eB (f a) = f' (eA a)) (hG : ∀ b, eC (g b) = g' (eB b))
    (hex : ∀ b', g' b' = 1 ↔ ∃ a', f' a' = b') (b : B) :
    g b = 1 ↔ ∃ a, f a = b := by
  constructor
  · intro hb
    have hb' : g' (eB b) = 1 := by rw [← hG b, hb, map_one]
    obtain ⟨a', ha'⟩ := (hex (eB b)).1 hb'
    refine ⟨eA.symm a', eB.injective ?_⟩
    rw [hF, eA.apply_symm_apply, ha']
  · rintro ⟨a, ha⟩
    apply eC.injective
    rw [map_one, hG, ← ha, hF]
    exact (hex (f' (eA a))).2 ⟨eA a, rfl⟩

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
