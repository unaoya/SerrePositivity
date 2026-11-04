module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericNil
public import Mathlib.RingTheory.Localization.Algebra

/-!
# 局所化後の nil な核を主開集合へ広げる

## 概要
有限生成な核が指定された局所化後に nil なら、一つの分母で nil になる。

## 方針
元の核の生成元の冪零関係の分母を払い、核と局所化の交換を使う。

## 規約
核は各元が冪零という意味の nil イデアル。

## 使われ方
対角射の核に適用して、一般点での普遍単射性を広げる。
-/

@[expose] public section
noncomputable section
universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.CommutativeAlgebra

/-- 局所化後に nil な有限生成核は、一つの分母を反転すれば nil。 -/
theorem exists_away_nil_kernel_of_localized_nil_kernel
    {R A B A' B' : Type u} [CommRing R] [CommRing A] [CommRing B]
    [CommRing A'] [CommRing B'] [Algebra R A] [Algebra R B]
    [Algebra R A'] [Algebra R B']
    (M : Submonoid R) (a : A →ₐ[R] A') (b : B →ₐ[R] B')
    [IsLocalizedModule M a.toLinearMap]
    (f : A →ₐ[R] B) (f' : A' →ₐ[R] B')
    (hcomm : f'.comp a = b.comp f) (hfg : (RingHom.ker f.toRingHom).FG)
    (hn : RingHom.ker f'.toRingHom ≤ nilradical A') :
    ∃ g : M, RingHom.ker (Localization.awayMap f.toRingHom (algebraMap R A g)) ≤
      nilradical (Localization.Away (algebraMap R A g)) := by
  obtain ⟨g, hg⟩ := exists_away_nil_of_localized_nil M a (RingHom.ker f.toRingHom) hfg
    (fun x hx ↦ mem_nilradical.mp (hn (by
      change f' (a x) = 0
      rw [← AlgHom.comp_apply, hcomm, AlgHom.comp_apply]
      change b (f x) = 0
      rw [show f x = 0 from hx, map_zero])))
  refine ⟨g, ?_⟩
  simp only [Localization.awayMap, IsLocalization.Away.map]
  rw [IsLocalization.ker_map (Localization.Away (f (algebraMap R A g)))
    f.toRingHom (Submonoid.map_powers f.toRingHom (algebraMap R A g))]
  exact hg

end SerrePositivity.CommutativeAlgebra
