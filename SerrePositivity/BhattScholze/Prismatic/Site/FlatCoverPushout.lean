module

public import SerrePositivity.BhattScholze.Prismatic.Site.FlatCover
public import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensor
import all SerrePositivity.BhattScholze.Prismatic.Site.FlatCover
import SerrePositivity.BhattScholze.Prism.Basic.Rigidity
import SerrePositivity.BhattScholze.Prism.Bounded.CompletelyFlatPrism
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# 完備テンソル積の prismatic site における押し出し性

## 概要
底変換した完備テンソル積の完全忠実平坦性と濃度評価から、site の押し出しを得る。

## 方針
基底の生成元の像を向きとする有界 prism を構成し、完備テンソル積の二脚の普遍性を使う。

## 規約
BS 著者版 Corollary 3.12 (a) の固定基底・向き付きの場合。完全忠実平坦性と濃度の評価は入力。

## 使われ方
平坦位相と増大 Čech 余脈体の構成。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PrismOver

open CategoryTheory CategoryTheory.Limits DerivedCompletion

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {R : Type u} [CommRing R] [Algebra (A ⧸ P.ideal) R] {κ : Cardinal.{u}}

/-- 概要：完全忠実平坦で濃度制限を満たす完備テンソル積は、site の押し出し。
方針：通常の δ 射の普遍性を prism イデアル・剰余の脚と両立させる。
規約：BS 著者版 Corollary 3.12 (a) の押し出しの普遍性。
使われ方：完全忠実平坦性と濃度を別途証明して、被覆の底変換を得る。 -/
theorem exists_isPushout_of_completedTensor_completelyFaithfullyFlat
    {X Y X' : PrismOver P R κ} (f : X ⟶ Y) (g : X ⟶ X')
    (hsmall : letI := f.toHom.toRingHom.toAlgebra; letI := g.toHom.toRingHom.toAlgebra
      Cardinal.mk (PrismCompletedTensor (A := X.B) (C := Y.B) X'.Q) ≤ κ)
    (hflat : letI := f.toHom.toRingHom.toAlgebra; letI := g.toHom.toRingHom.toAlgebra
      let T := PrismCompletedTensor (A := X.B) (C := Y.B) X'.Q
      let u : X'.B →+* T := prismCompletedTensorLeft X'.Q
      letI := u.toAlgebra
      IsCompletelyFaithfullyFlat (Ideal.span {(p : X'.B), X'.Q.generator}) T) :
    ∃ (Y' : PrismOver P R κ) (f' : X' ⟶ Y') (g' : Y ⟶ Y'),
      IsPushout f g g' f' ∧ IsFaithfullyFlat f' := by
  let := f.toHom.toRingHom.toAlgebra
  let := g.toHom.toRingHom.toAlgebra
  let T := PrismCompletedTensor (A := X.B) (C := Y.B) X'.Q
  let l : X'.B →+* T := prismCompletedTensorLeft X'.Q
  let r : Y.B →+* T := prismCompletedTensorRight X'.Q
  let D := prismCompletedTensorDelta X'.Q X.Q.deltaStructure Y.Q.deltaStructure
    g.toHom.map_delta f.toHom.map_delta
  have hl : X'.Q.deltaStructure.IsDeltaHom D l :=
    prismCompletedTensorLeft_isDeltaHom X'.Q X.Q.deltaStructure Y.Q.deltaStructure
      g.toHom.map_delta f.toHom.map_delta
  have hr : Y.Q.deltaStructure.IsDeltaHom D r :=
    prismCompletedTensorRight_isDeltaHom X'.Q X.Q.deltaStructure Y.Q.deltaStructure
      g.toHom.map_delta f.toHom.map_delta
  have hw : l.comp g.toHom.toRingHom = r.comp f.toHom.toRingHom :=
    prismCompletedTensor_square X'.Q
  obtain ⟨Q, u, hD, hd, hu, hQ⟩ := exists_boundedPrism_of_completelyFlat_deltaAlgebra X'.Q
    X'.bounded D l hl (prismCompletedTensor_complete_p X'.Q)
    (prismCompletedTensor_complete_generator X'.Q) hflat.1
  have hrI : Y.Q.ideal ≤ Q.ideal.comap r := by
    rw [← f.toHom.span_map_generator, Ideal.span_le]
    apply Set.singleton_subset_iff.mpr
    change (r.comp f.toHom.toRingHom) X.Q.generator ∈ Q.ideal
    rw [← hw]
    change l (g.toHom.toRingHom X.Q.generator) ∈ Q.ideal
    rw [← hu]
    exact u.ideal_le (g.toHom.map_generator_mem)
  let v : OrientedPrism.Hom Y.Q Q := ⟨r, by rw [hD]; exact hr, hrI⟩
  have hw' : v.comp f.toHom = u.comp g.toHom := by
    apply OrientedPrism.Hom.ext
    change r.comp f.toHom.toRingHom = u.toRingHom.comp g.toHom.toRingHom
    rw [hu, hw]
  let Y' : PrismOver P R κ :=
    { B := T
      Q := Q
      bounded := hQ
      toHom := u.comp X'.toHom
      sec := u.quotientMap.comp X'.sec
      sec_comp := by rw [RingHom.comp_assoc, X'.sec_comp, OrientedPrism.Hom.quotientMap_comp]
      small := hsmall }
  let f' : X' ⟶ Y' := ⟨u, rfl, rfl⟩
  let g' : Y ⟶ Y' :=
    { toHom := v
      comm_base := by
        change v.comp Y.toHom = u.comp X'.toHom
        rw [← f.comm_base, ← g.comm_base, ← OrientedPrism.Hom.comp_assoc,
          hw', OrientedPrism.Hom.comp_assoc]
      comm_sec := by
        change v.quotientMap.comp Y.sec = u.quotientMap.comp X'.sec
        rw [← f.comm_sec, ← g.comm_sec, ← RingHom.comp_assoc, ← RingHom.comp_assoc,
          ← OrientedPrism.Hom.quotientMap_comp, hw', OrientedPrism.Hom.quotientMap_comp] }
  have hs : f ≫ g' = g ≫ f' := PrismOver.Hom.ext hw'
  have hex (s : PushoutCocone f g) :
      ∃ k : Y' ⟶ s.pt, g' ≫ k = s.inl ∧ f' ≫ k = s.inr := by
    have hsc : s.inr.toHom.toRingHom.comp g.toHom.toRingHom =
        s.inl.toHom.toRingHom.comp f.toHom.toRingHom :=
      congrArg (fun a : X ⟶ s.pt ↦ a.toHom.toRingHom) s.condition.symm
    obtain ⟨k, hk, _⟩ := existsUnique_prismCompletedTensorHom X'.Q X.Q.deltaStructure
      Y.Q.deltaStructure g.toHom.map_delta f.toHom.map_delta s.pt.Q.deltaStructure
      s.inr.toHom.toRingHom s.inl.toHom.toRingHom s.inr.toHom.map_delta s.inl.toHom.map_delta
      hsc s.pt.Q.complete_p s.inr.toHom.isModuleComplete_map_generator
    have hkl : k.comp l = s.inr.toHom.toRingHom := hk.2.1
    have hkr : k.comp r = s.inl.toHom.toRingHom := hk.2.2
    let w : OrientedPrism.Hom Q s.pt.Q :=
      ⟨k, by rw [hD]; exact hk.1, by
        rw [OrientedPrism.ideal, hd, Ideal.span_le]
        apply Set.singleton_subset_iff.mpr
        change (k.comp l) X'.Q.generator ∈ s.pt.Q.ideal
        rw [hkl]
        exact s.inr.toHom.map_generator_mem⟩
    have hwu : w.comp u = s.inr.toHom := by
      apply OrientedPrism.Hom.ext
      change k.comp u.toRingHom = _
      rw [hu]
      exact hkl
    have hwv : w.comp v = s.inl.toHom := OrientedPrism.Hom.ext hkr
    let j : Y' ⟶ s.pt :=
      { toHom := w
        comm_base := by
          change w.comp (u.comp X'.toHom) = s.pt.toHom
          rw [← OrientedPrism.Hom.comp_assoc, hwu, s.inr.comm_base]
        comm_sec := by
          change w.quotientMap.comp (u.quotientMap.comp X'.sec) = s.pt.sec
          rw [← RingHom.comp_assoc, ← OrientedPrism.Hom.quotientMap_comp, hwu, s.inr.comm_sec] }
    exact ⟨j, PrismOver.Hom.ext hwv, PrismOver.Hom.ext hwu⟩
  refine ⟨Y', f', g', ⟨⟨hs⟩, ⟨?_⟩⟩, ?_⟩
  · refine PushoutCocone.IsColimit.mk _ (fun s ↦ (hex s).choose)
      (fun s ↦ (hex s).choose_spec.1) (fun s ↦ (hex s).choose_spec.2) ?_
    intro s k hk₁ hk₂
    let j := (hex s).choose
    have h₁ := hk₁.trans (hex s).choose_spec.1.symm
    have h₂ := hk₂.trans (hex s).choose_spec.2.symm
    apply PrismOver.Hom.ext
    apply OrientedPrism.Hom.ext
    apply prismCompletedTensorHom_ext X'.Q X.Q.deltaStructure Y.Q.deltaStructure
      g.toHom.map_delta f.toHom.map_delta s.pt.Q.deltaStructure
      (by
        change D.IsDeltaHom s.pt.Q.deltaStructure k.toHom.toRingHom
        rw [← hD]
        exact k.toHom.map_delta) (by
        change D.IsDeltaHom s.pt.Q.deltaStructure j.toHom.toRingHom
        rw [← hD]
        exact j.toHom.map_delta)
    · change k.toHom.toRingHom.comp l = j.toHom.toRingHom.comp l
      rw [← hu]
      exact congrArg (fun a : X' ⟶ s.pt ↦ a.toHom.toRingHom) h₂
    · exact congrArg (fun a : Y ⟶ s.pt ↦ a.toHom.toRingHom) h₁
    · exact s.pt.Q.complete_p
    · have h := congrArg (fun a : X' ⟶ s.pt ↦ a.toHom.toRingHom) (hex s).choose_spec.2
      change j.toHom.toRingHom.comp u.toRingHom = s.inr.toHom.toRingHom at h
      rw [hu] at h
      change IsModuleComplete s.pt.B ((j.toHom.toRingHom.comp l) X'.Q.generator) _
      rw [h]
      exact s.inr.toHom.isModuleComplete_map_generator
  · unfold IsFaithfullyFlat
    change (letI := u.toRingHom.toAlgebra
      IsCompletelyFaithfullyFlat (Ideal.span {(p : X'.B), X'.Q.generator}) T)
    rw [hu]
    exact hflat

end SerrePositivity.BhattScholze.Prismatic.PrismOver
