module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prismatic.Site.FlatCechComparison
import all SerrePositivity.BhattScholze.Prismatic.Site.FlatCover
import SerrePositivity.BhattScholze.Prism.Basic.Rigidity
import SerrePositivity.BhattScholze.Prism.Bounded.CompletionFiniteResidue
import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorCover
import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorCardinal
import SerrePositivity.BhattScholze.Prism.Bounded.CompletelyFlatPrism
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Algebra.Category.Ring.Constructions
import SerrePositivity.CategoryTheory.FiniteWidePushoutMap

/-!
# Site の平坦押し出しの有限剰余

## 概要
基底から延長した有限剰余で、site の平坦押し出しは通常の環の押し出しになる。

## 方針
完備テンソル積の二脚と任意の site の押し出しを比較し、有限剰余の普遍性を移す。

## 規約
BS 著者版 Corollary 3.12。有限剰余とは p と prism の生成元の冪を含むもの。

## 使われ方
平坦被覆の完備 Čech 余脈体の項別の有限剰余比較。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PrismOver

open CategoryTheory CategoryTheory.Limits DerivedCompletion
open scoped Cardinal TensorProduct

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {R : Type u} [CommRing R] [Algebra (A ⧸ P.ideal) R] {κ : Cardinal.{u}}

private abbrev ringMap {X Y : PrismOver P R κ} (f : X ⟶ Y) :=
  (structureRing (P := P) (R := R) (κ := κ)).map f

-- 完備テンソル積と site の押し出しの台環を照合するため。
set_option maxHeartbeats 850000 in
/-- 概要：平坦な site の押し出しの台環は、二脚を保つ完備テンソル積と同型。
方針：完備テンソル積の δ 射の普遍性を使い、site の押し出しと相互に比較する。
規約：BS 著者版 Corollary 3.12 (a)。許容濃度を固定する。
使われ方：有限剰余の比較と基底変換での台環の同定。 -/
theorem exists_completedTensor_pushoutEquiv (hκ : IsAdmissibleCutoff P R κ)
    {X Y X' Z : PrismOver P R κ} (f : X ⟶ Y) (g : X ⟶ X')
    (hf : IsFaithfullyFlat f) {i : Y ⟶ Z} {j : X' ⟶ Z}
    (hsq : IsPushout f g i j) :
    letI := f.toHom.toRingHom.toAlgebra
    letI := g.toHom.toRingHom.toAlgebra
    ∃ e : (PrismCompletedTensor (A := X.B) (C := Y.B) X'.Q) ≃+* Z.B,
      e.toRingHom.comp (prismCompletedTensorLeft X'.Q) = j.toHom.toRingHom ∧
      e.toRingHom.comp (prismCompletedTensorRight X'.Q) = i.toHom.toRingHom := by
  let := f.toHom.toRingHom.toAlgebra
  let := g.toHom.toRingHom.toAlgebra
  let T := PrismCompletedTensor (A := X.B) (C := Y.B) X'.Q
  let l : X'.B →+* T := prismCompletedTensorLeft X'.Q
  let := l.toAlgebra
  have hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : X'.B), X'.Q.generator}) T :=
    prismCompletedTensor_completelyFaithfullyFlat X.Q X'.Q X'.bounded
      g.toHom f.toHom.toRingHom hf
  let D := prismCompletedTensorDelta X'.Q X.Q.deltaStructure Y.Q.deltaStructure
    g.toHom.map_delta f.toHom.map_delta
  have hl := prismCompletedTensorLeft_isDeltaHom X'.Q X.Q.deltaStructure Y.Q.deltaStructure
    g.toHom.map_delta f.toHom.map_delta
  let r : Y.B →+* T := prismCompletedTensorRight X'.Q
  have hr : Y.Q.deltaStructure.IsDeltaHom D r :=
    prismCompletedTensorRight_isDeltaHom X'.Q X.Q.deltaStructure Y.Q.deltaStructure
      g.toHom.map_delta f.toHom.map_delta
  have hw : l.comp g.toHom.toRingHom = r.comp f.toHom.toRingHom :=
    prismCompletedTensor_square X'.Q
  obtain ⟨Q, u, hD, hd, hu, hQ⟩ := exists_boundedPrism_of_completelyFlat_deltaAlgebra X'.Q
    X'.bounded D l hl (prismCompletedTensor_complete_p X'.Q)
    (prismCompletedTensor_complete_generator X'.Q) hflat.1
  have hc : IsAdicComplete (Ideal.span {(p : T), l X'.Q.generator}) T := by
    rw [← hd]
    exact _root_.SerrePositivity.BhattScholze.boundedPrism_pair_isAdicComplete Q hQ
  have hκ₀ : ℵ₀ ≤ κ := by
    apply le_trans ?_ hκ.1
    unfold cutoff
    apply le_trans ?_ (Cardinal.self_le_power _ Cardinal.one_le_aleph0)
    rw [add_comm]
    exact le_self_add
  have hsmall := prismCompletedTensor_mk_le X'.Q hκ₀ hκ.2 X'.small Y.small hc
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
  let a := hsq.desc g' f' hs
  obtain ⟨b, hb₁', hb₂'⟩ := hex hsq.cocone
  have hb₁ : g' ≫ b = i := hb₁'
  have hb₂ : f' ≫ b = j := hb₂'
  have ha₁ : i ≫ a = g' := hsq.inl_desc _ _ _
  have ha₂ : j ≫ a = f' := hsq.inr_desc _ _ _
  have hab : a ≫ b = 𝟙 Z := by
    apply hsq.hom_ext
    · rw [← Category.assoc, ha₁, hb₁]
      simp
    · rw [← Category.assoc, ha₂, hb₂]
      simp
  have hba : b ≫ a = 𝟙 Y' := by
    apply PrismOver.Hom.ext
    apply OrientedPrism.Hom.ext
    apply prismCompletedTensorHom_ext X'.Q X.Q.deltaStructure Y.Q.deltaStructure
      g.toHom.map_delta f.toHom.map_delta Q.deltaStructure
      (by
        change D.IsDeltaHom Q.deltaStructure (b ≫ a).toHom.toRingHom
        rw [← hD]
        exact (b ≫ a).toHom.map_delta)
      (by
        change D.IsDeltaHom Q.deltaStructure (PrismOver.Hom.toHom (𝟙 Y')).toRingHom
        rw [← hD]
        exact (PrismOver.Hom.toHom (𝟙 Y')).map_delta)
    · have hh : f' ≫ (b ≫ a) = f' ≫ 𝟙 Y' := by rw [← Category.assoc, hb₂, ha₂, Category.comp_id]
      change (b ≫ a).toHom.toRingHom.comp l = (PrismOver.Hom.toHom (𝟙 Y')).toRingHom.comp l
      rw [← hu]
      exact congrArg (fun k : X' ⟶ Y' ↦ k.toHom.toRingHom) hh
    · have hh : g' ≫ (b ≫ a) = g' ≫ 𝟙 Y' := by rw [← Category.assoc, hb₁, ha₁, Category.comp_id]
      exact congrArg (fun k : Y ⟶ Y' ↦ k.toHom.toRingHom) hh
    · exact Q.complete_p
    · exact prismCompletedTensor_complete_generator X'.Q
  let e : T ≃+* Z.B :=
    RingEquiv.ofRingHom b.toHom.toRingHom a.toHom.toRingHom
      (congrArg (fun k : Z ⟶ Z ↦ k.toHom.toRingHom) hab)
      (congrArg (fun k : Y' ⟶ Y' ↦ k.toHom.toRingHom) hba)
  refine ⟨e, ?_, ?_⟩
  · change b.toHom.toRingHom.comp l = j.toHom.toRingHom
    rw [← hu]
    exact congrArg (fun k : X' ⟶ Z ↦ k.toHom.toRingHom) hb₂
  · exact congrArg (fun k : Y ⟶ Z ↦ k.toHom.toRingHom) hb₁

-- 完備テンソル積とその有限剰余の型を照合するため。
set_option maxHeartbeats 2400000 in
/-- 概要：site の平坦押し出しを基底から延長したイデアルで剰余すると環の押し出し。
方針：実際の完備テンソル積へ移し、有限剰余比較をその二脚に適用する。
規約：BS 著者版 Corollary 3.12。p と向きの冪がイデアルに入ると仮定する。
使われ方：有限広押し出しと完備 Čech 余脈体の比較。 -/
theorem isPushout_flatResidueRing (hκ : IsAdmissibleCutoff P R κ)
    {X Y X' Z : PrismOver P R κ} (f : X ⟶ Y) (g : X ⟶ X')
    (hf : IsFaithfullyFlat f) {i : Y ⟶ Z} {j : X' ⟶ Z}
    (hsq : IsPushout f g i j) (J : Ideal X.B) (m n : ℕ)
    (hp : (p : X.B) ^ m ∈ J) (hd₀ : X.Q.generator ^ n ∈ J) :
    IsPushout (flatResidueArrow f J).hom (flatResidueArrow g J).hom
      ((flatResidueRing J).map (Under.homMk (U := Under.mk f)
        (V := Under.mk (f ≫ i)) i rfl))
      ((flatResidueRing J).map (Under.homMk (U := Under.mk g)
        (V := Under.mk (f ≫ i)) j hsq.w.symm)) := by
  let := f.toHom.toRingHom.toAlgebra
  let := g.toHom.toRingHom.toAlgebra
  obtain ⟨e, hel, her⟩ := exists_completedTensor_pushoutEquiv hκ f g hf hsq
  let U := X'.B ⊗[X.B] Y.B
  let l₀ : X'.B →+* U := Algebra.TensorProduct.includeLeftRingHom
  have hpU : (p : U) ^ m ∈ J.map (algebraMap X.B U) := by
    simpa only [map_pow, map_natCast] using Ideal.mem_map_of_mem (algebraMap X.B U) hp
  obtain ⟨v₀, hv₀⟩ := g.toHom.map_generator_unit_mul
  have hgen : algebraMap X.B U X.Q.generator = l₀ X'.Q.generator * l₀ v₀ := by
    rw [← map_mul, ← hv₀]
    exact (Algebra.TensorProduct.includeLeft.commutes X.Q.generator).symm
  have hdU : (l₀ X'.Q.generator) ^ n ∈ J.map (algebraMap X.B U) := by
    have h := Ideal.mem_map_of_mem (algebraMap X.B U) hd₀
    rw [map_pow, hgen, mul_pow] at h
    have hu' : IsUnit (l₀ (v₀ : X'.B) ^ n) := (v₀.isUnit.map l₀).pow n
    obtain ⟨u₀, hu₀⟩ := hu'
    have h' := (J.map (algebraMap X.B U)).mul_mem_left (↑u₀⁻¹ : U) h
    rwa [← hu₀, mul_left_comm, Units.inv_mul, mul_one] at h'
  let T := PrismCompletedTensor (A := X.B) (C := Y.B) X'.Q
  let t : U →+* T := pdCompletionUnit U p (l₀ X'.Q.generator)
  let tZ : U →+* Z.B := e.toRingHom.comp t
  let lZ : CommRingCat.of X'.B ⟶ CommRingCat.of U := CommRingCat.ofHom l₀
  let r₀ : Y.B →+* U := Algebra.TensorProduct.includeRight.toRingHom
  let rZ : CommRingCat.of Y.B ⟶ CommRingCat.of U := CommRingCat.ofHom r₀
  let uZ : CommRingCat.of U ⟶ CommRingCat.of Z.B := CommRingCat.ofHom tZ
  let J₀ := J.map (algebraMap X.B U)
  let h₀ := CommRingCat.isPushout_tensorProduct X.B X'.B Y.B
  obtain ⟨q, hq⟩ := exists_pdCompletion_finiteResidue_equiv p (l₀ X'.Q.generator) J₀ m n hpU hdU
  have hJ₀ : J₀ = J.map (ringMap g ≫ lZ).hom := by congr 1
  have hJ₁ : J.map ((ringMap g ≫ lZ) ≫ uZ).hom = (J₀.map t).map e.toRingHom := by
    rw [hJ₀, Ideal.map_map, Ideal.map_map] <;> rfl
  let e₁ := Ideal.quotEquivOfEq hJ₀.symm
  let e₂ := Ideal.quotientEquiv (J₀.map t) _ e hJ₁
  have hq' (x : U) : q.symm (Ideal.Quotient.mk J₀ x) =
      Ideal.Quotient.mk (J₀.map t) (t x) := by
    apply q.injective
    exact (q.apply_symm_apply _).trans (RingHom.congr_fun hq x).symm
  let eQ : (U ⧸ J.map (ringMap g ≫ lZ).hom) ≃+*
      (Z.B ⧸ J.map ((ringMap g ≫ lZ) ≫ uZ).hom) :=
    e₁.trans (q.symm.trans e₂)
  have heQ (x : U) : eQ (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (tZ x) := by
    change e₂ (q.symm (Ideal.Quotient.mk J₀ x)) = _
    rw [hq'] <;> rfl
  have hfinite₀ := @isPushout_residue_postcompose
    (CommRingCat.of X.B) (CommRingCat.of X'.B) (CommRingCat.of Y.B)
    (CommRingCat.of U) (CommRingCat.of Z.B) J
    (ringMap g) (ringMap f) lZ rZ h₀ uZ eQ heQ
  have hfinite := hfinite₀.flip
  have hlZ : lZ ≫ uZ = ringMap j := CommRingCat.hom_ext hel
  have hrZ : rZ ≫ uZ = ringMap i := CommRingCat.hom_ext her
  have heq : ringMap (f ≫ i) = (ringMap g ≫ lZ) ≫ uZ := by
    calc
      ringMap (f ≫ i) = ringMap (g ≫ j) := congrArg (fun a : X ⟶ Z ↦ ringMap a) hsq.w
      _ = ringMap g ≫ ringMap j := (structureRing (P := P) (R := R) (κ := κ)).map_comp g j
      _ = _ := by rw [Category.assoc, hlZ]
  let eI := Ideal.quotEquivOfEq
    (congrArg (fun k : CommRingCat.of X.B ⟶ CommRingCat.of Z.B ↦ J.map k.hom) heq.symm)
  let eBase := Ideal.quotientEquiv J (J.map (RingHom.id X.B)) (RingEquiv.refl X.B) rfl
  refine hfinite.of_iso eBase.toCommRingCatIso (Iso.refl _) (Iso.refl _) eI.toCommRingCatIso ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id]
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    change Ideal.Quotient.mk _ (f.toHom.toRingHom x) =
      Ideal.Quotient.mk _ (((Under.mkIdInitial (X := X)).to (Under.mk f)).right.toHom.toRingHom x)
    rw [Under.mkIdInitial_to_right] <;> rfl
  · simp only [Iso.refl_hom, Category.comp_id]
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    change Ideal.Quotient.mk _ (g.toHom.toRingHom x) =
      Ideal.Quotient.mk _ (((Under.mkIdInitial (X := X)).to (Under.mk g)).right.toHom.toRingHom x)
    rw [Under.mkIdInitial_to_right] <;> rfl
  · simp only [Iso.refl_hom, Category.id_comp]
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro y
    change Ideal.Quotient.mk _ ((rZ ≫ uZ).hom y) = Ideal.Quotient.mk _ ((ringMap i).hom y)
    rw [hrZ] <;> rfl
  · simp only [Iso.refl_hom, Category.id_comp]
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro y
    change Ideal.Quotient.mk _ ((lZ ≫ uZ).hom y) = Ideal.Quotient.mk _ ((ringMap j).hom y)
    rw [hlZ] <;> rfl

/-- 概要：平坦な被覆の完備 Čech 項の有限剰余は通常の広押し出し。
方針：二項押し出しの有限剰余保存を各脚の追加に適用する。
規約：BS 著者版 Corollary 3.12 (c)。p と生成元の冪を含む基底イデアル。
使われ方：完備 Čech 余脈体と有限剰余の Čech 完全性の比較。 -/
def flatResidueCoconeIsColimit (hκ : IsAdmissibleCutoff P R κ)
    {X Y : PrismOver P R κ} (f : X ⟶ Y) (hf : IsFaithfullyFlat f)
    (J : Ideal X.B) (m n : ℕ) (hp : (p : X.B) ^ m ∈ J)
    (hd : X.Q.generator ^ n ∈ J) (k : SimplexCategory) :
    IsColimit (flatResidueCocone hκ f hf J k) := by
  letI := hasWidePushout_flat hκ f hf (k.len + 1)
  let hc := isColimit_mapRepeatedWideCocone (flatResidueRing J) f
    (fun {_} g ↦ by
      obtain ⟨_, _, _, h, _⟩ := exists_isPushout_isFaithfullyFlat hκ f hf g
      exact h.hasPushout)
    (fun {_ _} g _ _ h ↦ isPushout_flatResidueRing hκ f g hf h J m n hp hd)
    (colimit.isColimit (repeatedWideSpan f (k.len + 1)))
  refine IsColimit.ofIsoColimit hc (Cocone.ext (Iso.refl _) ?_)
  rintro (_ | j)
  · simp only [Iso.refl_hom, Category.comp_id]
    change (flatResidueRing J).map _ = (flatResidueRing J).map _
    congr 1
    exact (Under.mkIdInitial (X := X)).hom_ext _ _
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl

end SerrePositivity.BhattScholze.Prismatic.PrismOver

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Cor 3.12" (partial := special) "固定基底 (A,(d)) 上・濃度 cutoff の site（D22）。(a) 完全平坦な押し出し、構造環と d 剰余の全次数の Čech 完全性と層条件（BS-W15 K4）。∞ 層・RΓ への接続は drafts ／ 11-11 更新（2） ／ 11-12 夜更新（§3 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.PrismOver.isPushout_flatResidueRing
