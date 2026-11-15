module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Semiperfectoid.Discrete.DiscretePrism
public import SerrePositivity.CategoryTheory.InitialOfRetraction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import SerrePositivity.CommutativeAlgebra.Adic.RingRetract
import SerrePositivity.BhattScholze.Prism.Basic.Rigidity

/-!
# Prismatic site の冪等完備性

## 概要
有界 prism の site で冪等射を分裂させ、自然な評価脚から始対象を得る。

## 方針
冪等射の固定環に δ 構造を制限する。二座標での完備性と剰余の有界性を分裂の両脚に沿って移す。

## 規約
BS 著者版 Lemma 7.8 の向き付き有界 prism の場合。p 正則な部分圏も扱う。

## 使われ方
離散な評価からの始対象の構成。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PrismOver

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SerrePositivity.DerivedCompletion

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {R : Type u} [CommRing R] [Algebra (A ⧸ P.ideal) R] {κ : Cardinal.{u}}

/-- 概要：site の冪等射は、元の環への単射を持つ有界 prism に分裂する。
方針：固定環を取り、基底から来る生成元で向きを指定する。
規約：BS 著者版 Lemma 7.8 の prismatic site。濃度制限も維持する。
使われ方：site 全体と p 正則な充満部分圏の冪等完備性。 -/
theorem exists_split_idempotent {X : PrismOver P R κ} (e : X ⟶ X) (he : e ≫ e = e) :
    ∃ (Y : PrismOver P R κ) (i : Y ⟶ X) (r : X ⟶ Y),
      i ≫ r = 𝟙 Y ∧ r ≫ i = e ∧ Function.Injective i.toHom.toRingHom := by
  let f := e.toHom.toRingHom
  have hf (x : X.B) : f (f x) = f x :=
    RingHom.congr_fun (congrArg (fun a : X ⟶ X ↦ a.toHom.toRingHom) he) x
  have hbase (x : A) : f (X.toHom.toRingHom x) = X.toHom.toRingHom x :=
    RingHom.congr_fun (congrArg OrientedPrism.Hom.toRingHom e.comm_base) x
  let S := f.eqLocus (RingHom.id X.B)
  let j : S →+* X.B := S.subtype
  let r : X.B →+* S := f.codRestrict S hf
  have hret : Function.LeftInverse r j := fun x ↦ Subtype.ext x.property
  have hS : ∀ x ∈ S, X.Q.deltaStructure.delta x ∈ S := by
    intro x hx
    change f x = x at hx
    change f (X.Q.deltaStructure.delta x) = X.Q.deltaStructure.delta x
    rw [e.toHom.map_delta x, hx]
  let D := X.Q.deltaStructure.subring S hS
  let η : A →+* S := X.toHom.toRingHom.codRestrict S hbase
  have hη : P.deltaStructure.IsDeltaHom D η := by
    intro x
    apply Subtype.ext
    exact X.toHom.map_delta x
  let a : S := η P.generator
  have ha : IsRegular a := by
    have hi : Function.Injective (fun x : S ↦ a * x) := by
      intro x y hxy
      apply Subtype.ext
      exact X.toHom.map_generator_mul_injective (congrArg Subtype.val hxy)
    exact ⟨hi, fun x y hxy ↦ hi (by simpa only [mul_comm] using hxy)⟩
  have hp : IsModuleComplete S (p : S) (ModuleCat.of S S) := by
    apply isModuleComplete_of_ring_retract j r hret
    simpa only [map_natCast] using X.Q.complete_p
  have hd : IsModuleComplete S a (ModuleCat.of S S) :=
    isModuleComplete_of_ring_retract j r hret a X.toHom.isModuleComplete_map_generator
  let Q := P.ofDiscreteDelta D η hη ha hp hd
  let b := P.toDiscreteDelta D η hη ha hp hd
  let iH : OrientedPrism.Hom Q X.Q :=
    ⟨j, X.Q.deltaStructure.subring_subtype_isDeltaHom S hS, by
      apply Ideal.span_le.mpr
      exact Set.singleton_subset_iff.mpr X.toHom.map_generator_mem⟩
  let rH : OrientedPrism.Hom X.Q Q :=
    ⟨r, (fun x ↦ Subtype.ext (e.toHom.map_delta x)), by
      rw [← X.toHom.span_map_generator, Ideal.span_le]
      apply Set.singleton_subset_iff.mpr
      change r (X.toHom.toRingHom P.generator) ∈ Q.ideal
      have h : r (X.toHom.toRingHom P.generator) = Q.generator :=
        Subtype.ext (hbase P.generator)
      rw [h]
      exact Ideal.subset_span (Set.mem_singleton _)⟩
  have hri : rH.comp iH = OrientedPrism.Hom.id Q :=
    OrientedPrism.Hom.ext (RingHom.ext hret)
  have hir : iH.comp rH = e.toHom := OrientedPrism.Hom.ext rfl
  have hb : b = rH.comp X.toHom :=
    OrientedPrism.Hom.ext (RingHom.ext fun x ↦ Subtype.ext (hbase x).symm)
  have hbi : iH.comp b = X.toHom := OrientedPrism.Hom.ext rfl
  have hq : rH.quotientMap.comp iH.quotientMap = RingHom.id (S ⧸ Q.ideal) := by
    rw [← OrientedPrism.Hom.quotientMap_comp, hri, OrientedPrism.Hom.quotientMap_id]
  have hbound : IsBoundedPrism Q := by
    obtain ⟨N, hN⟩ := X.bounded
    refine ⟨N, fun n x hx ↦ ?_⟩
    have hsplit : Function.LeftInverse rH.quotientMap iH.quotientMap := RingHom.congr_fun hq
    have hi : Function.Injective iH.quotientMap := hsplit.injective
    apply hi
    have hx' : (p : X.B ⧸ X.Q.ideal) ^ n * iH.quotientMap x = 0 := by
      simpa only [map_mul, map_pow, map_natCast, map_zero] using congrArg iH.quotientMap hx
    simpa only [map_mul, map_pow, map_natCast, map_zero] using hN n (iH.quotientMap x) hx'
  let Y : PrismOver P R κ :=
    { B := S
      Q := Q
      bounded := hbound
      toHom := b
      sec := rH.quotientMap.comp X.sec
      sec_comp := by rw [RingHom.comp_assoc, X.sec_comp, ← OrientedPrism.Hom.quotientMap_comp, ← hb]
      small := (Cardinal.mk_le_of_injective (f := j) Subtype.val_injective).trans X.small }
  let i' : Y ⟶ X := ⟨iH, hbi, by
    change iH.quotientMap.comp (rH.quotientMap.comp X.sec) = X.sec
    rw [← RingHom.comp_assoc, ← OrientedPrism.Hom.quotientMap_comp, hir, e.comm_sec]⟩
  let r' : X ⟶ Y := ⟨rH, hb.symm, rfl⟩
  exact ⟨Y, i', r', PrismOver.Hom.ext hri, PrismOver.Hom.ext hir, Subtype.val_injective⟩

/-- 概要：有界 prism の site は冪等完備。
方針：固定環への分裂を取る。
規約：BS 著者版 Lemma 7.8 の環側の圏。
使われ方：自然な評価から始対象を作る。 -/
theorem isIdempotentComplete : IsIdempotentComplete (PrismOver P R κ) :=
  ⟨fun _ e he ↦ by
    obtain ⟨Y, i, r, hir, hri, _⟩ := exists_split_idempotent e he
    exact ⟨Y, i, r, hir, hri⟩⟩

/-- 台の環が p 正則である site の対象。 -/
abbrev primeRegular : ObjectProperty (PrismOver P R κ) :=
  fun X ↦ IsRegular (p : X.B)

/-- 概要：p 正則な対象の充満部分圏は冪等完備。
方針：分裂先の台環は元の台環に単射で写るので p の正則性が移る。
規約：Lemma 7.7 (3) の p 正則な対象の評価範囲。
使われ方：自然な評価が定まる範囲で Lemma 7.8 を適用する。 -/
theorem primeRegular_isIdempotentComplete :
    IsIdempotentComplete (primeRegular (P := P) (R := R) (κ := κ)).FullSubcategory := by
  constructor
  intro X e he
  have he' : e.hom ≫ e.hom = e.hom := congrArg (fun a ↦ a.hom) he
  obtain ⟨Y, i, r, hir, hri, hi⟩ := exists_split_idempotent e.hom he'
  have hleft : Function.Injective (fun x : Y.B ↦ (p : Y.B) * x) := by
    intro x y h
    apply hi
    exact X.property.left (by
      simpa only [map_mul, map_natCast] using congrArg i.toHom.toRingHom h)
  let Z : (primeRegular (P := P) (R := R) (κ := κ)).FullSubcategory :=
    ⟨Y, ⟨hleft, fun x y h ↦ hleft (by simpa only [mul_comm] using h)⟩⟩
  exact ⟨Z, ObjectProperty.homMk i, ObjectProperty.homMk r,
    InducedCategory.hom_ext hir, InducedCategory.hom_ext hri⟩

/-- 概要：p 正則な site 上に自然な評価族があれば、同じ部分圏に始対象を得る。
方針：評価族の源での冪等自己射を固定環に分裂させる。
規約：BS 著者版 Lemma 7.7–7.8 の古典環の適用。
使われ方：自然な評価を持つ離散模型。 -/
theorem exists_initial_of_primeRegular_evaluation
    (X : (primeRegular (P := P) (R := R) (κ := κ)).FullSubcategory)
    (ev : ∀ Y : (primeRegular (P := P) (R := R) (κ := κ)).FullSubcategory, X ⟶ Y)
    (hn : ∀ {Y Z : (primeRegular (P := P) (R := R) (κ := κ)).FullSubcategory}
      (f : Y ⟶ Z), ev Y ≫ f = ev Z) :
    ∃ (Y : (primeRegular (P := P) (R := R) (κ := κ)).FullSubcategory), Nonempty (IsInitial Y) := by
  let := primeRegular_isIdempotentComplete (P := P) (R := R) (κ := κ)
  obtain ⟨Y, _, _, _, _, hY⟩ := initial_of_natural_legs X ev hn
  exact ⟨Y, hY⟩

end SerrePositivity.BhattScholze.Prismatic.PrismOver

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 7.7" (partial := component) "BS-W15 K5（11-11）：離散な場合の δ 構造の一意性、離散な prism と Frobenius からの射、p 正則な部分圏での始性は本体。導来 prismatic コホモロジー Δ_R/A との同一視（G10、∞ 側）は drafts の A3/DiscreteCase"] _root_.SerrePositivity.BhattScholze.Prismatic.PrismOver.exists_initial_of_primeRegular_evaluation
attribute [cite BS19 "Lemma 7.8"] _root_.SerrePositivity.BhattScholze.Prismatic.PrismOver.exists_split_idempotent
attribute [cite BS19 "Lemma 7.8"] _root_.SerrePositivity.BhattScholze.Prismatic.PrismOver.isIdempotentComplete
