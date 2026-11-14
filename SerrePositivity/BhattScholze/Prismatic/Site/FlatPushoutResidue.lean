module

public import SerrePositivity.BhattScholze.Prismatic.Site.FlatTopologyPushout
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# 完備押し出しの有限剰余

## 概要
座標の冪を含むイデアルで剰余を取ると、完備テンソル積の二脚は通常の環の押し出しになる。

## 方針
通常のテンソル積の剰余を押し出しとして扱い、完備化の有限剰余同型を二脚とともに移す。

## 規約
BS 著者版 Corollary 3.12 の有限剰余の比較。イデアルは基底から延長する。

## 使われ方
prismatic site の完備 Čech 余脈体を有限剰余の通常の余脈体と比較する。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open CategoryTheory CategoryTheory.Limits DerivedCompletion
open scoped TensorProduct

/-- 基底のイデアルによる剰余の間の誘導射。 -/
abbrev residueHom {A B : CommRingCat.{u}} (I : Ideal A) (f : A ⟶ B) :
    CommRingCat.of (A ⧸ I) ⟶ CommRingCat.of (B ⧸ I.map f.hom) :=
  CommRingCat.ofHom (Ideal.quotientMap _ f.hom (Ideal.map_le_iff_le_comap.mp le_rfl))

/-- 延長イデアルによる剰余の間の誘導射。 -/
abbrev residueLeg {A B C : CommRingCat.{u}} (I : Ideal A) (f : A ⟶ B) (g : A ⟶ C)
    (i : B ⟶ C) (hi : f ≫ i = g) :
    CommRingCat.of (B ⧸ I.map f.hom) ⟶ CommRingCat.of (C ⧸ I.map g.hom) :=
  CommRingCat.ofHom (Ideal.quotientMap _ i.hom (by
    apply Ideal.map_le_iff_le_comap.mp
    rw [Ideal.map_map]
    exact (congrArg (fun z : A ⟶ C ↦ I.map z.hom) hi).le))

/-- 概要：環の押し出しの全頂点で同じ基底イデアルによる剰余を取っても押し出しになる。
方針：二脚を商写像と合成して元の押し出しの普遍性を使い、得た射を剰余に降ろす。
規約：通常の可換環の押し出し。
使われ方：BS 著者版 Corollary 3.12 の有限剰余の比較。 -/
theorem isPushout_residue {A B C T : CommRingCat.{u}} (I : Ideal A)
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ T} {j : C ⟶ T}
    (h : IsPushout f g i j) :
    IsPushout (residueHom I f) (residueHom I g)
      (residueLeg I f (f ≫ i) i rfl) (residueLeg I g (f ≫ i) j h.w.symm) := by
  let f₀ := residueHom I f
  let g₀ := residueHom I g
  let i₀ := residueLeg I f (f ≫ i) i rfl
  let j₀ := residueLeg I g (f ≫ i) j h.w.symm
  let qB := CommRingCat.ofHom (Ideal.Quotient.mk (I.map f.hom))
  let qC := CommRingCat.ofHom (Ideal.Quotient.mk (I.map g.hom))
  let qT := CommRingCat.ofHom (Ideal.Quotient.mk (I.map (f ≫ i).hom))
  have hw : f₀ ≫ i₀ = g₀ ≫ j₀ := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext a
    exact congrArg (fun z : A ⟶ T ↦ qT.hom (z.hom a)) h.w
  refine ⟨⟨hw⟩, ⟨?_⟩⟩
  have hs (s : PushoutCocone f₀ g₀) : f ≫ (qB ≫ s.inl) = g ≫ (qC ≫ s.inr) := by
    apply CommRingCat.hom_ext
    ext a
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom s.condition)
      (Ideal.Quotient.mk I a)
  let k (s : PushoutCocone f₀ g₀) := h.desc (qB ≫ s.inl) (qC ≫ s.inr) (hs s)
  have hk (s : PushoutCocone f₀ g₀) : I.map (f ≫ i).hom ≤ RingHom.ker (k s).hom := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change ((f ≫ i) ≫ k s).hom a = 0
    rw [Category.assoc, show i ≫ k s = qB ≫ s.inl by simp [k]]
    change s.inl.hom (qB.hom (f.hom a)) = 0
    rw [show qB.hom (f.hom a) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f.hom ha), map_zero]
  let d (s : PushoutCocone f₀ g₀) :=
    CommRingCat.ofHom (Ideal.Quotient.lift _ (k s).hom (fun _ ha ↦ hk s ha))
  refine PushoutCocone.IsColimit.mk _ d ?_ ?_ ?_
  · intro s
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext b
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom
      (h.inl_desc (qB ≫ s.inl) (qC ≫ s.inr) (hs s))) b
  · intro s
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext c
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom
      (h.inr_desc (qB ≫ s.inl) (qC ≫ s.inr) (hs s))) c
  · intro s e he₁ he₂
    have he : qT ≫ e = k s := by
      apply h.hom_ext
      · rw [← Category.assoc, show i ≫ qT = qB ≫ i₀ from rfl,
          Category.assoc, he₁]
        simp [k]
      · rw [← Category.assoc, show j ≫ qT = qC ≫ j₀ from rfl,
          Category.assoc, he₂]
        simp [k]
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    exact congrArg CommRingCat.Hom.hom he

/-- 概要：終点の剰余が同型なら、両脚を保つ比較を通じて剰余の押し出しを移せる。
方針：通常の剰余押し出しを、代表元上で二脚と可換な環同型に沿って移す。
規約：イデアルは共通の基底から延長する。
使われ方：完備テンソル積の有限剰余。 -/
theorem isPushout_residue_postcompose {A B C T H : CommRingCat.{u}} (I : Ideal A)
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ T} {j : C ⟶ T}
    (h : IsPushout f g i j) (u : T ⟶ H)
    (e : (T ⧸ I.map (f ≫ i).hom) ≃+* (H ⧸ I.map ((f ≫ i) ≫ u).hom))
    (he : ∀ x : T, e (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (u.hom x)) :
    IsPushout (residueHom I f) (residueHom I g)
      (residueLeg I f ((f ≫ i) ≫ u) (i ≫ u) (Category.assoc _ _ _).symm)
      (residueLeg I g ((f ≫ i) ≫ u) (j ≫ u) (by rw [← Category.assoc, h.w])) := by
  refine (isPushout_residue I h).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    e.toCommRingCatIso (by simp) (by simp) ?_ ?_
  · apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext b
    exact he (i.hom b)
  · apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext c
    exact he (j.hom c)

end SerrePositivity.BhattScholze.Prismatic
