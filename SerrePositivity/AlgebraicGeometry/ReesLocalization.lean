module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.ReesMap
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Localization.Algebra

/-!
概要：KST §5 の Rees 代数と係数環の局所化の両立に必要な分母消去。
方針：有限個の係数ごとにイデアルの冪の中で分母を払い、共通分母を取る。
規約：任意の乗法的集合と可換環の局所化を用いる。
使われ方：blowup の開基底変更との比較と一般スキームへの貼り合わせ。
-/

@[expose] public noncomputable section

universe u v
namespace SerrePositivity.AlgebraicGeometry
open Polynomial
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  [Algebra R S] (M : Submonoid R) [IsLocalization M S] (I : Ideal R)

/--
概要：局所化した中心の Rees 代数の元は、係数環の一つの分母で元の Rees 代数に戻る。
方針：各係数を Iⁿ の元として持ち上げ、有限個の分母の積を共通分母にする。
規約：KST §5、元の環で分母が非零因子であることは不要。
使われ方：Rees 代数自体の局所化の全射条件。
-/
theorem rees_localization_clear_denominator
    (p : reesAlgebra (I.map (algebraMap R S))) :
    ∃ m : M, ∃ q : reesAlgebra I,
      p.1 * C (algebraMap R S m.1) = q.1.map (algebraMap R S) := by
  classical
  have hcoeff (n : ℕ) : p.1.coeff n ∈ (I ^ n).map (algebraMap R S) := by
    rw [Ideal.map_pow]
    exact p.2 n
  choose c hc using fun n => (IsLocalization.mem_map_algebraMap_iff M S).mp (hcoeff n)
  let m : M := ∏ n ∈ p.1.support, (c n).2
  let d (n : ℕ) : R := ∏ j ∈ p.1.support.erase n, ((c j).2 : R)
  let q : reesAlgebra I := ∑ n ∈ p.1.support,
    reesMonomial I n ⟨((c n).1 : R) * d n, Ideal.mul_mem_right _ _ (c n).1.2⟩
  refine ⟨m, q, ?_⟩
  have hm (n : ℕ) (hn : n ∈ p.1.support) :
      (m : R) = ((c n).2 : R) * d n := by
    dsimp only [m, d]
    rw [Submonoid.coe_finsetProd]
    exact (Finset.mul_prod_erase _ _ hn).symm
  calc
    p.1 * C (algebraMap R S m.1) =
        (∑ n ∈ p.1.support, monomial n (p.1.coeff n)) * C (algebraMap R S m.1) := by
          rw [← p.1.as_sum_support]
    _ = ∑ n ∈ p.1.support, monomial n (p.1.coeff n * algebraMap R S m.1) := by
      rw [Finset.sum_mul]
      simp only [monomial_mul_C]
    _ = ∑ n ∈ p.1.support, monomial n (algebraMap R S (((c n).1 : R) * d n)) := by
      apply Finset.sum_congr rfl
      intro n hn
      congr 1
      rw [hm n hn, map_mul, ← mul_assoc, hc n, map_mul]
    _ = q.1.map (algebraMap R S) := by
      change _ = (Polynomial.mapRingHom (algebraMap R S)) ((reesAlgebra I).val q)
      dsimp only [q]
      rw [map_sum]
      simp only [map_sum, reesMonomial, Subalgebra.val_apply, Polynomial.coe_mapRingHom,
        Polynomial.map_monomial]

set_option backward.isDefEq.respectTransparency false in
/--
概要：局所化した中心の Rees 代数は、元の Rees 代数を定数分母で局所化した環。
方針：単元条件と分母消去に加え、多項式環の局所化から等式の検出条件を移す。
規約：KST §5、実際の Rees 係数写像について普遍的な局所化条件を証明する。
使われ方：開基底変更上の blowup の同型の環論的入力。
-/
theorem reesMap_isLocalizationMap :
    (M.map (algebraMap R (reesAlgebra I))).IsLocalizationMap
      (reesMap I (I.map (algebraMap R S)) (algebraMap R S) le_rfl) where
  map_units := by
    rintro ⟨_, r, hr, rfl⟩
    rw [reesMap_base]
    exact (IsLocalization.map_units S ⟨r, hr⟩).map
      (algebraMap S (reesAlgebra (I.map (algebraMap R S))))
  surj p := by
    obtain ⟨m, q, h⟩ := rees_localization_clear_denominator M I p
    refine ⟨⟨q, ⟨algebraMap R (reesAlgebra I) m.1, ⟨m.1, m.2, rfl⟩⟩⟩, ?_⟩
    rw [reesMap_base]
    exact Subtype.ext h
  exists_of_eq := by
    intro p q h
    let : Algebra R[X] S[X] := Polynomial.algebra R S
    let : IsLocalization (M.map (C : R →+* R[X])) S[X] := Polynomial.isLocalization M S
    have h' : algebraMap R[X] S[X] p.1 = algebraMap R[X] S[X] q.1 :=
      congrArg Subtype.val h
    obtain ⟨⟨d, hd⟩, hd'⟩ := (IsLocalization.eq_iff_exists
      (M.map (C : R →+* R[X])) S[X]).mp h'
    obtain ⟨m, hm, rfl⟩ := hd
    refine ⟨⟨algebraMap R (reesAlgebra I) m, ⟨m, hm, rfl⟩⟩, ?_⟩
    exact Subtype.ext hd'

/--
概要：定数分母による Rees 代数の局所化と、局所化した中心の Rees 代数の環同型。
方針：同じ Rees 係数写像の局所化を実現する二つの環を普遍性で比較する。
規約：KST §5、局所化の実現を実際の環同型として固定する。
使われ方：Proj の開基底変更の比較の環論的モデル。
-/
def reesLocalizationEquiv :
    Localization (M.map (algebraMap R (reesAlgebra I))) ≃+*
      reesAlgebra (I.map (algebraMap R S)) := by
  let : Algebra (reesAlgebra I) (reesAlgebra (I.map (algebraMap R S))) :=
    (reesMap I (I.map (algebraMap R S)) (algebraMap R S) le_rfl).toAlgebra
  let : IsLocalization (M.map (algebraMap R (reesAlgebra I)))
      (reesAlgebra (I.map (algebraMap R S))) :=
    (isLocalization_iff_isLocalizationMap _ _).mpr (reesMap_isLocalizationMap M I)
  exact (IsLocalization.algEquiv (M.map (algebraMap R (reesAlgebra I)))
    (Localization (M.map (algebraMap R (reesAlgebra I))))
    (reesAlgebra (I.map (algebraMap R S)))).toRingEquiv

/--
概要：Rees 局所化の環同型は元の Rees 代数からの係数写像を保存する。
方針：局所化間の代数同型の係数保存則を適用する。
規約：KST §5、分母一の元についての等式。
使われ方：標準チャート上の射と基底の交換式。
-/
@[simp] theorem reesLocalizationEquiv_base (p : reesAlgebra I) :
    reesLocalizationEquiv M I
      (algebraMap (reesAlgebra I) (Localization (M.map (algebraMap R (reesAlgebra I)))) p) =
        reesMap I (I.map (algebraMap R S)) (algebraMap R S) le_rfl p := by
  let : Algebra (reesAlgebra I) (reesAlgebra (I.map (algebraMap R S))) :=
    (reesMap I (I.map (algebraMap R S)) (algebraMap R S) le_rfl).toAlgebra
  let : IsLocalization (M.map (algebraMap R (reesAlgebra I)))
      (reesAlgebra (I.map (algebraMap R S))) :=
    (isLocalization_iff_isLocalizationMap _ _).mpr (reesMap_isLocalizationMap M I)
  exact (IsLocalization.algEquiv (M.map (algebraMap R (reesAlgebra I)))
    (Localization (M.map (algebraMap R (reesAlgebra I))))
    (reesAlgebra (I.map (algebraMap R S)))).commutes p

/--
概要：局所化した Rees 代数の斉次元の分母は、同じ次数の元の中で払える。
方針：共通分母で持ち上げた多項式の指定次数の係数だけを取る。
規約：KST §5、分母は零次の定数元、斉次次数は任意。
使われ方：標準 blowup チャートと係数局所化の両立。
-/
theorem rees_localization_clear_homogeneous (n : ℕ)
    (p : reesAlgebra (I.map (algebraMap R S))) (hp : p ∈ reesGrade _ n) :
    ∃ m : M, ∃ q : reesAlgebra I, q ∈ reesGrade I n ∧
      p * algebraMap S (reesAlgebra (I.map (algebraMap R S))) (algebraMap R S m.1) =
        reesMap I (I.map (algebraMap R S)) (algebraMap R S) le_rfl q := by
  obtain ⟨m, q, hq⟩ := rees_localization_clear_denominator M I p
  refine ⟨m, reesMonomial I n ⟨q.1.coeff n, q.2 n⟩, reesMonomial_mem I n _, ?_⟩
  apply Subtype.ext
  change p.1 * C (algebraMap R S m.1) =
    (monomial n (q.1.coeff n)).map (algebraMap R S)
  have hcoeff := congrArg (fun v : S[X] => v.coeff n) hq
  simp only [coeff_mul_C, coeff_map] at hcoeff
  rw [(mem_reesGrade_iff _ _ _).mp hp, monomial_mul_C, Polynomial.map_monomial, hcoeff]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
