module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.Distinguished.Universal
public import SerrePositivity.BhattScholze.Prism.Basic.Bounded
public import SerrePositivity.BhattScholze.Prism.Basic.GeneratorRegularity
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaPDCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Pair.PrincipalPairRegularity

/-!
# 普遍向き付き prism

## 概要
BS 著者版 Example 3.4 の有界な普遍向き付き prism とその正則性。

## 方針
普遍 distinguished 環を p と d で導来完備化し、正則対の完備化の結果を使う。

## 規約
普遍性では標的の選択した生成元への像を指定する。

## 使われ方
向き付き prism への普遍な底環を与える。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.BhattScholze

open DerivedCompletion

variable (p : ℕ) [Fact p.Prime]

/-- 概要：普遍向き付き prism の台環。
方針：未完備な普遍 distinguished 環の二元導来完備化の H⁰。
規約：BS 著者版 Example 3.4。
使われ方：普遍 prism と mod p の Frobenius の定義。 -/
abbrev UniversalOrientedPrismRing :=
  PDCompletionH0 (UniversalDistinguishedRing.{u} p) p (universalDistinguishedGenerator p)

instance universalOrientedPrismCommRing : CommRing (UniversalOrientedPrismRing.{u} p) :=
  pdCompletionCommRing _ p (universalDistinguishedGenerator p)

/-- 概要：普遍向き付き prism。
方針：完備化で第二元の正則性と distinguished 性を保つ。
規約：BS 著者版 Example 3.4。
使われ方：向き付き prism の指定生成元を表現する。 -/
def universalOrientedPrism : OrientedPrism p (UniversalOrientedPrismRing.{u} p) :=
  let L := UniversalDistinguishedRing.{u} p
  let d := universalDistinguishedGenerator.{u} p
  let D := universalDistinguishedDelta.{u} p
  let j := pdCompletionUnit L p d
  OrientedPrism.ofDistinguished (deltaPDCompletionStructure D d) (j d)
    ((pdCompletionUnit_isDeltaHom D d).map_isDistinguished
      (universalDistinguishedGenerator_isDistinguished p))
    (Andre.principalPair_pairCompletion_second_regular (p : L) d
      (universalDistinguished_regular p).1 (universalDistinguished_regular p).2)
    (pdCompletionH0_self_complete_p L p d)
    (pdCompletionH0_self_complete_d L p d)

/-- 概要：普遍向き付き prism で d を殺した商は p 正則。
方針：正則対の二元完備化の第二剰余で第一元を消去できる。
規約：BS 著者版 Example 3.4。
使われ方：有界性と (p,d) の正則性。 -/
theorem universalOrientedPrism_mod_generator_p_regular :
    let Q := UniversalOrientedPrismRing.{u} p ⧸ (universalOrientedPrism p).ideal
    IsSMulRegular Q (p : Q) := by
  let L := UniversalDistinguishedRing.{u} p
  let U := UniversalOrientedPrismRing.{u} p
  let d := universalDistinguishedGenerator.{u} p
  let j := pdCompletionUnit L p d
  let I : Ideal U := (universalOrientedPrism p).ideal
  let q := Ideal.Quotient.mk I
  have h : IsSMulRegular (U ⧸ I) (q (j (p : L))) :=
    Andre.principalPair_pairCompletion_mod_second_first_regular (p : L) d
      (universalDistinguished_regular p).1 (universalDistinguished_regular p).2
  rw [map_natCast j, map_natCast q] at h
  exact h

/-- 概要：普遍向き付き prism は有界。
方針：生成元で割った商で p の全ての冪が正則。
規約：BS 著者版 Example 3.4。
使われ方：有界 prism 上の構成への適用。 -/
theorem universalOrientedPrism_bounded :
    Prismatic.IsBoundedPrism (universalOrientedPrism.{u} p) := by
  let Q := UniversalOrientedPrismRing.{u} p ⧸ (universalOrientedPrism p).ideal
  refine ⟨0, fun n (x : Q) hx ↦ ?_⟩
  have hz := (universalOrientedPrism_mod_generator_p_regular.{u} p).pow n
  have he : (p : Q) ^ n • x = (p : Q) ^ n • 0 := by
    simpa only [smul_eq_mul, mul_zero] using hx
  simpa only [pow_zero, one_mul] using hz he

/-- 概要：普遍向き付き prism の (p,d) は弱正則。
方針：完備化で p の正則性を保ち、d 商での p の正則性から順序を入れ替える。
規約：BS 著者版 Example 3.4。
使われ方：mod p の Frobenius の d 完全平坦性の判定。 -/
theorem universalOrientedPrism_regular :
    let U := UniversalOrientedPrismRing.{u} p
    let I := Ideal.span {(p : U)}
    IsSMulRegular U (p : U) ∧
      IsSMulRegular (U ⧸ I) (Ideal.Quotient.mk I (universalOrientedPrism p).generator) := by
  let L := UniversalDistinguishedRing.{u} p
  let U := UniversalOrientedPrismRing.{u} p
  let d := universalDistinguishedGenerator.{u} p
  let j := pdCompletionUnit L p d
  have h : IsSMulRegular U (j (p : L)) :=
    Andre.principalPair_pairCompletion_first_regular (p : L) d
      (universalDistinguished_regular p).1 (universalDistinguished_regular p).2
  rw [map_natCast j] at h
  exact ⟨h, Andre.perfectPrism_generator_modPrime_regular (universalOrientedPrism p)
    (universalOrientedPrism_mod_generator_p_regular p)⟩

private theorem isUnit_natCast_of_coprime {A : Type u} [CommRing A]
    (P : OrientedPrism p A) (n : ℕ) (hn : Nat.Coprime n p) : IsUnit (n : A) := by
  have hab := Nat.gcd_eq_gcd_ab n p
  rw [show Nat.gcd n p = 1 from hn] at hab
  have ha : (1 : A) = (n : A) * (Nat.gcdA n p : A) + (p : A) * (Nat.gcdB n p : A) := by
    change (1 : ℤ) = _ at hab
    simpa only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast] using
      congrArg (fun z : ℤ ↦ (z : A)) hab
  have hu := (Ideal.mem_jacobson_bot.mp P.p_mem_jacobson) (-((Nat.gcdB n p : ℤ) : A))
  have he : (p : A) * -((Nat.gcdB n p : ℤ) : A) + 1 =
      (n : A) * ((Nat.gcdA n p : ℤ) : A) := by
    rw [mul_neg, ha]
    abel
  rw [he] at hu
  exact isUnit_of_mul_isUnit_left hu

/-- 概要：普遍向き付き prism からの生成元を保つ射は一意に存在する。
方針：未完備の評価を標的の p および生成元での導来完備性で延長する。
規約：BS 著者版 Example 3.4 の向きを保つ普遍性。
使われ方：向き付き prism の標準的な底変換。 -/
theorem existsUnique_universalOrientedPrismHom {A : Type u} [CommRing A]
    (P : OrientedPrism p A) :
    ∃! f : OrientedPrism.Hom (universalOrientedPrism.{u} p) P,
      f.toRingHom (universalOrientedPrism p).generator = P.generator := by
  let d := universalDistinguishedGenerator.{u} p
  let D := universalDistinguishedDelta.{u} p
  obtain ⟨g, hg, hgu⟩ := existsUnique_universalDistinguishedHom p
    P.deltaStructure P.generator P.isDistinguished_generator (isUnit_natCast_of_coprime p P)
  obtain ⟨h, hh, hhu⟩ := existsUnique_deltaPDCompletionHom D d P.deltaStructure g hg.1
    P.complete_p (hg.2 ▸ P.complete_generator)
  have hd : h (universalOrientedPrism p).generator = P.generator :=
    (DFunLike.congr_fun hh.2 d).trans hg.2
  let f : OrientedPrism.Hom (universalOrientedPrism.{u} p) P :=
    { toRingHom := h
      map_delta := hh.1
      ideal_le := by
        rw [OrientedPrism.ideal, Ideal.span_singleton_le_iff_mem]
        change h (universalOrientedPrism p).generator ∈ P.ideal
        rw [hd]
        exact Ideal.subset_span (Set.mem_singleton _) }
  refine ⟨f, hd, fun k hk ↦ OrientedPrism.Hom.ext (hhu k.toRingHom ⟨k.map_delta, ?_⟩)⟩
  exact hgu _ ⟨k.map_delta.comp (pdCompletionUnit_isDeltaHom D d), hk⟩

end SerrePositivity.BhattScholze

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Ex 3.4"] _root_.SerrePositivity.BhattScholze.existsUnique_universalOrientedPrismHom
attribute [cite BS19 "Ex 3.4"] _root_.SerrePositivity.BhattScholze.universalOrientedPrism
attribute [cite BS19 "Ex 3.4"] _root_.SerrePositivity.BhattScholze.universalOrientedPrism_bounded
