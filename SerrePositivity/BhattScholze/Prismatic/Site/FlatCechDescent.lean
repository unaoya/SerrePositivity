module
public meta import SerrePositivity.Util.Citation

public import SerrePositivity.BhattScholze.Prismatic.Site.FlatCechLimit
import SerrePositivity.BhattScholze.Prism.Bounded.Completeness
import SerrePositivity.CommutativeAlgebra.Adic.CompatibleResidues

/-!
# 構造環の完備 Čech 降下

## 概要
平坦な被覆について、構造環と prism イデアルによる剰余の増大完備 Čech 複体は全次数で完全。

## 方針
有界 prism の古典的完備性を用い、各項を有限剰余の逆極限として計算する。

## 規約
BS 著者版 Corollary 3.12 (c) の古典的な増大 Čech 完全性と環値の層条件。

## 使われ方
固定基底の prismatic site の構造層とその剰余。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PrismOver

open CategoryTheory CategoryTheory.Limits

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {R : Type u} [CommRing R] [Algebra (A ⧸ P.ideal) R] {κ : Cardinal.{u}}
variable {X Y : PrismOver P R κ}

private theorem primeIdeal_map (f : X ⟶ Y) :
    (Ideal.span {(p : X.B)}).map f.toHom.toRingHom = Ideal.span {(p : Y.B)} := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

private theorem pairIdeal_map (f : X ⟶ Y) :
    (flatPairIdeal X).map f.toHom.toRingHom = flatPairIdeal Y := by
  rw [flatPairIdeal, ← Set.singleton_union, Ideal.span_union, Ideal.map_sup, primeIdeal_map]
  change Ideal.span {(p : Y.B)} ⊔ X.Q.ideal.map f.toHom.toRingHom = _
  rw [f.toHom.map_ideal_eq, OrientedPrism.ideal, ← Ideal.span_union, Set.singleton_union]

private def structureToResidue (J : Ideal X.B) :
    Under.forget X ⋙ structureRing ⟶ flatResidueRing J where
  app Z := CommRingCat.ofHom (Ideal.Quotient.mk (J.map Z.hom.toHom.toRingHom))
  naturality := by
    intro U V f
    rfl

private def quotientToResidue (J : Ideal X.B) (h : X.Q.ideal ≤ J) :
    Under.forget X ⋙ quotientStructureRing ⟶ flatResidueRing J where
  app Z := CommRingCat.ofHom (Ideal.Quotient.factor (by
    change Z.right.Q.ideal ≤ J.map Z.hom.toHom.toRingHom
    rw [← Z.hom.toHom.map_ideal_eq]
    exact Ideal.map_mono h))
  naturality := by
    intro U V k
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext x
    rfl

private abbrev reducedIdeal (X : PrismOver P R κ) (n : ℕ) : Ideal X.B :=
  X.Q.ideal ⊔ (Ideal.span {(p : X.B)}) ^ n

private theorem reducedIdeal_antitone (X : PrismOver P R κ) : Antitone (reducedIdeal X) :=
  fun _ _ h ↦ sup_le_sup_left (Ideal.pow_le_pow_right h) _

private theorem pairPow_le_reducedIdeal (X : PrismOver P R κ) (n : ℕ) :
    flatPairIdeal X ^ (1 + n) ≤ reducedIdeal X n := by
  have h : flatPairIdeal X = X.Q.ideal ⊔ Ideal.span {(p : X.B)} := by
    rw [OrientedPrism.ideal, ← Ideal.span_union, Set.singleton_union, Ideal.span_pair_comm]
  rw [h]
  simpa only [pow_one] using
    (Ideal.sup_pow_add_le_pow_sup_pow (I := X.Q.ideal)
      (J := Ideal.span {(p : X.B)}) (n := 1) (m := n))

private def reducedResidueIso (Z : Under X) (n : ℕ) :
    (Z.right.B ⧸ Z.right.Q.ideal) ⧸
      (Ideal.span {(p : Z.right.B ⧸ Z.right.Q.ideal)}) ^ n ≃+*
        (flatResidueRing (reducedIdeal X n)).obj Z := by
  let Q := Z.right.Q
  let T := Ideal.span {(p : Z.right.B)}
  have hT : (T ^ n).map (Ideal.Quotient.mk Q.ideal) =
      (Ideal.span {(p : Z.right.B ⧸ Q.ideal)}) ^ n := by
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast]
  have hZ : Q.ideal ⊔ T ^ n = (reducedIdeal X n).map Z.hom.toHom.toRingHom := by
    rw [reducedIdeal, Ideal.map_sup, Ideal.map_pow, Z.hom.toHom.map_ideal_eq, primeIdeal_map]
  exact (Ideal.quotEquivOfEq hT.symm).trans
    ((DoubleQuot.quotQuotEquivQuotSup Q.ideal (T ^ n)).trans (Ideal.quotEquivOfEq hZ))

/-- 概要：構造環の増大完備 Čech 複体は全次数で完全。
方針：各項を (p,d) の冪による有限剰余の逆極限で復元する。
規約：BS 著者版 Corollary 3.12 (c)。
使われ方：構造前層の層条件。 -/
theorem structureRing_flatCechExact (hκ : IsAdmissibleCutoff P R κ)
    (f : X ⟶ Y) (hf : IsFaithfullyFlat f) :
    Cech.AugmentedRingCechExact (flatRingCech hκ structureRing f hf) := by
  let J (n : ℕ) := flatPairIdeal X ^ n
  have hJ : Antitone J := fun _ _ h ↦ Ideal.pow_le_pow_right h
  refine flatRingCechExact_of_residues hκ f hf structureRing J hJ (fun n ↦ ⟨n, le_rfl⟩)
    (fun n ↦ structureToResidue (J n)) ?_ ?_
  · intro n
    ext Z x
    rfl
  · intro Z a ha
    let I := (flatPairIdeal X).map Z.hom.toHom.toRingHom
    letI : IsAdicComplete I Z.right.B := by
      change IsAdicComplete ((flatPairIdeal X).map Z.hom.toHom.toRingHom) Z.right.B
      rw [pairIdeal_map]
      exact _root_.SerrePositivity.BhattScholze.boundedPrism_pair_isAdicComplete Z.right.Q Z.right.bounded
    let e (n : ℕ) : Z.right.B ⧸ I ^ n ≃+* (flatResidueRing (J n)).obj Z :=
      Ideal.quotEquivOfEq ((Ideal.map_pow _ _ _).symm)
    have hcompat (n : ℕ) (x : Z.right.B ⧸ I ^ (n + 1)) :
        e n (Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ) x) =
          (flatResidueTransition (hJ n.le_succ)).app Z (e (n + 1) x) := by
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    have h (n : ℕ) : Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ)
        ((e (n + 1)).symm (a (n + 1))) = (e n).symm (a n) := by
      apply (e n).injective
      rw [hcompat, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, ha]
    obtain ⟨z, hz, hu⟩ := existsUnique_of_compatible_idealResidues I (fun n ↦ (e n).symm (a n)) h
    refine ⟨z, fun n ↦ ?_, fun b hb ↦ hu b (fun n ↦ ?_)⟩
    · exact ((e n).toEquiv.eq_symm_apply).mp (hz n)
    · exact ((e n).toEquiv.eq_symm_apply).mpr (hb n)

/-- 概要：prism イデアルで剰余した構造環の増大完備 Čech 複体は全次数で完全。
方針：各項の p 完備性で (d,pⁿ) による剰余の逆極限を取り、有限段で忠実平坦降下を使う。
規約：BS 著者版 Corollary 3.12 (c) の通常の環と余鎖複体。
使われ方：剰余構造前層の層条件。 -/
theorem quotientStructureRing_flatCechExact (hκ : IsAdmissibleCutoff P R κ)
    (f : X ⟶ Y) (hf : IsFaithfullyFlat f) :
    Cech.AugmentedRingCechExact (flatRingCech hκ quotientStructureRing f hf) := by
  let J := reducedIdeal X
  have hJ := reducedIdeal_antitone X
  let π (n : ℕ) := quotientToResidue (J n) le_sup_left
  refine flatRingCechExact_of_residues hκ f hf quotientStructureRing J hJ
    (fun n ↦ ⟨1 + n, pairPow_le_reducedIdeal X n⟩) π ?_ ?_
  · intro n
    apply NatTrans.ext
    funext Z
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext x
    rfl
  · intro Z a ha
    let Q := Z.right.Q
    let I := Ideal.span {(p : Z.right.B ⧸ Q.ideal)}
    letI : IsAdicComplete I (Z.right.B ⧸ Q.ideal) :=
      _root_.SerrePositivity.BhattScholze.boundedPrism_quotient_isAdicComplete_prime Q Z.right.bounded
    let e := reducedResidueIso Z
    have hcompat (n : ℕ) (x : (Z.right.B ⧸ Q.ideal) ⧸ I ^ (n + 1)) :
        e n (Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ) x) =
          (flatResidueTransition (hJ n.le_succ)).app Z (e (n + 1) x) := by
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
      rfl
    have h (n : ℕ) : Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ)
        ((e (n + 1)).symm (a (n + 1))) = (e n).symm (a n) := by
      apply (e n).injective
      rw [hcompat, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, ha]
    have hπ (n : ℕ) (b : Z.right.B ⧸ Q.ideal) :
        e n (Ideal.Quotient.mk (I ^ n) b) = (π n).app Z b := by
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
      rfl
    obtain ⟨z, hz, hu⟩ := existsUnique_of_compatible_idealResidues I (fun n ↦ (e n).symm (a n)) h
    refine ⟨z, fun n ↦ ?_, fun b hb ↦ hu b (fun n ↦ ?_)⟩
    · rw [← hπ, hz, RingEquiv.apply_symm_apply]
    · apply ((e n).toEquiv.eq_symm_apply).mpr
      change e n (Ideal.Quotient.mk (I ^ n) b) = a n
      rw [hπ, hb]

/-- 構造環の前層は平坦位相の層（BS 著者版 Corollary 3.12 (c)）。 -/
theorem structureRing_isSheaf (hκ : IsAdmissibleCutoff P R κ) :
    Presheaf.IsSheaf (flatTopology hκ) (unopUnop _ ⋙ structureRing) :=
  isSheaf_of_flatRingCechExact hκ structureRing (fun {_ _} f hf ↦ structureRing_flatCechExact hκ f hf)

/-- prism イデアルによる剰余の前層は平坦位相の層（BS 著者版 Corollary 3.12 (c)）。 -/
theorem quotientStructureRing_isSheaf (hκ : IsAdmissibleCutoff P R κ) :
    Presheaf.IsSheaf (flatTopology hκ) (unopUnop _ ⋙ quotientStructureRing) :=
  isSheaf_of_flatRingCechExact hκ quotientStructureRing (fun {_ _} f hf ↦ quotientStructureRing_flatCechExact hκ f hf)

end SerrePositivity.BhattScholze.Prismatic.PrismOver

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Cor 3.12" (partial := special) "固定基底 (A,(d)) 上・濃度 cutoff の site（D22）。(a) 完全平坦な押し出し、構造環と d 剰余の全次数の Čech 完全性と層条件（BS-W15 K4）。∞ 層・RΓ への接続は drafts ／ 11-11 更新（2） ／ 11-12 夜更新（§3 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.PrismOver.quotientStructureRing_isSheaf
attribute [cite BS19 "Cor 3.12" (partial := special) "固定基底 (A,(d)) 上・濃度 cutoff の site（D22）。(a) 完全平坦な押し出し、構造環と d 剰余の全次数の Čech 完全性と層条件（BS-W15 K4）。∞ 層・RΓ への接続は drafts ／ 11-11 更新（2） ／ 11-12 夜更新（§3 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.PrismOver.structureRing_isSheaf
