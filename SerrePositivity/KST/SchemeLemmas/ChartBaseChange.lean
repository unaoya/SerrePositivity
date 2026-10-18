module

public import SerrePositivity.KST.SchemeLemmas.ChartAlgebra
public import SerrePositivity.KST.SchemeLemmas.ReesLocalization

/-!
概要：KST §5 の標準 blowup チャートの係数環に関する写像。
方針：Rees 代数の次数付き写像を斉次局所化し、中心元の像を分母とする。
規約：環準同型は任意、局所化に必要な仮定は該当する宣言だけに置く。
使われ方：係数環の局所化によるチャートの比較。
-/

@[expose] public noncomputable section

universe u v
namespace SerrePositivity.KST.SchemeLemmas
open Polynomial HomogeneousLocalization
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I.map f ≤ J)

/--
概要：中心を保つ環準同型による中心元の像。
方針：像イデアルへの所属から標的の中心への所属を得る。
規約：KST §5、標準チャートの添字を移す。
使われ方：チャート環の比較準同型。
-/
def centerImageElement (a : I) : J := ⟨f a.1, hf (Ideal.mem_map_of_mem f a.2)⟩

/--
概要：中心を保つ係数写像による標準 blowup チャート環の比較写像。
方針：Rees の次数付き写像を、中心元とその像の冪で斉次局所化する。
規約：KST §5、標的のチャートは中心元の実際の像に対応する。
使われ方：開基底変更における局所化環の同定。
-/
def chartBaseChangeMap (a : I) : BlowupChartRing I a →+*
    BlowupChartRing J (centerImageElement I J f hf a) :=
  HomogeneousLocalization.map (reesGradedMap I J f hf) (by
    apply Submonoid.powers_le.mpr
    refine ⟨1, ?_⟩
    dsimp only
    rw [pow_one]
    exact (reesMap_degreeOne I J f hf a).symm)

/--
概要：チャート比較写像は基礎環からの係数写像を保存する。
方針：零次の分母一の分数を、斉次局所化の写像で計算する。
規約：KST §5、基礎環は f により移る。
使われ方：標準チャートの Spec の比較射の基底両立性。
-/
@[simp] theorem chartBaseChangeMap_base (a : I) (r : R) :
    chartBaseChangeMap I J f hf a (chartBaseMap I a r) =
      chartBaseMap J (centerImageElement I J f hf a) (f r) := by
  simp only [chartBaseChangeMap, chartBaseMap, RingHom.comp_apply]
  change HomogeneousLocalization.map _ _ (HomogeneousLocalization.mk _) =
    HomogeneousLocalization.mk _
  rw [HomogeneousLocalization.map_mk]
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.val_mk, reesGradedMap, reesMap, reesZeroEquiv]
  rfl

/--
概要：チャート比較写像の斉次分数に対する計算式。
方針：分子と分母に Rees 写像を適用し、次数一分母の像を同定する。
規約：KST §5、分母の指数と分子の次数は一致する。
使われ方：局所化したチャートでの分母消去。
-/
theorem chartBaseChangeMap_mk (a : I) (k : ℕ) (p : reesAlgebra I)
    (hp : p ∈ reesGrade I (k * 1)) :
    chartBaseChangeMap I J f hf a (Away.mk (reesGrade I) (reesDegreeOne_mem I a) k p hp) =
      Away.mk (reesGrade J) (reesDegreeOne_mem J (centerImageElement I J f hf a)) k
        (reesMap I J f hf p) ((reesGradedMap I J f hf).map_mem hp) := by
  apply HomogeneousLocalization.val_injective
  simp only [chartBaseChangeMap, Away.mk, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk]
  congr 1
  apply Subtype.ext
  change (reesGradedMap I J f hf) (reesDegreeOne I a ^ k) =
    reesDegreeOne J (centerImageElement I J f hf a) ^ k
  rw [map_pow]
  exact congrArg (fun z => z ^ k) (reesMap_degreeOne I J f hf a)

section Localization
variable [Algebra R S] (M : Submonoid R) [IsLocalization M S]

/--
概要：係数局所化後の標準チャートの元は一つの係数分母で元のチャートから来る。
方針：斉次分数の分子を同次数の Rees 元で持ち上げる。
規約：KST §5、分母は基底環の乗法的集合 M の元。
使われ方：チャート比較写像が係数の局所化を実現することの全射条件。
-/
theorem chart_localization_clear_denominator (a : I)
    (z : BlowupChartRing (I.map (algebraMap R S))
      (centerImageElement I _ (algebraMap R S) le_rfl a)) :
    ∃ m : M, ∃ q : BlowupChartRing I a,
      z * chartBaseMap _ _ (algebraMap R S m.1) =
        chartBaseChangeMap I _ (algebraMap R S) le_rfl a q := by
  obtain ⟨k, p, hp, rfl⟩ := Away.mk_surjective _ (reesDegreeOne_mem _ _) z
  obtain ⟨m, q, hq, heq⟩ := rees_localization_clear_homogeneous M I (k * 1) p hp
  refine ⟨m, Away.mk (reesGrade I) (reesDegreeOne_mem I a) k q hq, ?_⟩
  rw [chartBaseChangeMap_mk]
  apply HomogeneousLocalization.val_injective
  rw [val_mul, chartBaseMap_val]
  simp only [Away.val_mk, Localization.mk_eq_mk']
  rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul]
  rw [mul_comm (algebraMap S (reesAlgebra (I.map (algebraMap R S))) (algebraMap R S m.1)) p, heq]
  erw [Away.val_mk, Localization.mk_eq_mk']

end Localization

end SerrePositivity.KST.SchemeLemmas
