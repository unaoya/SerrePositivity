module

public import SerrePositivity.CommutativeAlgebra.RootTower.Stage
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.CharP.Reduced

/-! # 有限段からmod pへの具体的なFrobenius射

基底係数aをa^(p^n) mod pへ、根の座標X_iをt_i mod pへ送る。
有限段の関係式を確認して射を定義し、pの根による商へ降ろす。
標準冪級数表示による全射性や商射の単射性は、この定義から自動的には主張しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.Section2
open MvPolynomial
variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    [CharP (A ⧸ Ideal.span {(p : A)}) p]

/-- 有限段の多項式表示に対するmod pのFrobenius評価。 -/
def stageModPFrobeniusAux (n : ℕ) : MvPolynomial (Fin h) A →+* A ⧸ Ideal.span {(p : A)} :=
  eval₂Hom ((iterateFrobenius (A ⧸ Ideal.span {(p : A)}) p n).comp
    (Ideal.Quotient.mk (Ideal.span {(p : A)})))
    (fun i ↦ Ideal.Quotient.mk (Ideal.span {(p : A)}) (t i))

/-- X_i^(p^n)-t_iはmod pのFrobenius評価で零になる。 -/
theorem towerRel_le_ker_stageModPFrobeniusAux (n : ℕ) :
    towerRel A t p n ≤ RingHom.ker (stageModPFrobeniusAux A t p n) := by
  change Ideal.span (Set.range (fun i ↦ (X i : MvPolynomial (Fin h) A) ^ (p ^ n) - C (t i))) ≤ _
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change stageModPFrobeniusAux A t p n ((X i) ^ (p ^ n) - C (t i)) = 0
  simp only [stageModPFrobeniusAux, map_sub, map_pow, eval₂Hom_X', eval₂Hom_C,
    RingHom.comp_apply, iterateFrobenius_def, sub_self]

/-- 有限段の環からA/pへの実際の射。 -/
def stageModPFrobenius (n : ℕ) : TowerStage A t p n →+* A ⧸ Ideal.span {(p : A)} :=
  Ideal.Quotient.lift (towerRel A t p n) (stageModPFrobeniusAux A t p n)
    (towerRel_le_ker_stageModPFrobeniusAux A t p n)

@[simp] theorem stageModPFrobenius_stageX (n : ℕ) (i : Fin h) :
    stageModPFrobenius A t p n (stageX A t p n i) =
      Ideal.Quotient.mk (Ideal.span {(p : A)}) (t i) := by
  exact eval₂Hom_X' _ _ _

@[simp] theorem stageModPFrobenius_algebraMap (n : ℕ) (a : A) :
    stageModPFrobenius A t p n (algebraMap A (TowerStage A t p n) a) =
      Ideal.Quotient.mk (Ideal.span {(p : A)}) a ^ (p ^ n) := by
  change stageModPFrobeniusAux A t p n (C a) = _
  exact eval₂Hom_C _ _ _

/-- 先頭として選んだ座標がpなら、そのp冪根の生成イデアルは射の核に入る。 -/
theorem span_stageRoot_le_ker_modPFrobenius (n : ℕ) (i : Fin h) (hti : t i = (p : A)) :
    Ideal.span {stageX A t p n i} ≤ RingHom.ker (stageModPFrobenius A t p n) := by
  rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, stageModPFrobenius_stageX, hti]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- pの根を零にした有限段の商からA/pへのFrobenius射。 -/
def stageRootModPFrobenius (n : ℕ) (i : Fin h) (hti : t i = (p : A)) :
    TowerStage A t p n ⧸ Ideal.span {stageX A t p n i} →+* A ⧸ Ideal.span {(p : A)} :=
  Ideal.Quotient.lift _ (stageModPFrobenius A t p n)
    (span_stageRoot_le_ker_modPFrobenius A t p n i hti)

@[simp] theorem stageRootModPFrobenius_mk (n : ℕ) (i : Fin h) (hti : t i = (p : A))
    (z : TowerStage A t p n) :
    stageRootModPFrobenius A t p n i hti (Ideal.Quotient.mk _ z) =
      stageModPFrobenius A t p n z := rfl

/-- 単射な商射が構成できれば、元の射の核はpの根の生成イデアルに一致する。 -/
theorem stageModPFrobenius_ker_of_quotient_injective
    (n : ℕ) (i : Fin h) (hti : t i = (p : A))
    (hf : Function.Injective (stageRootModPFrobenius A t p n i hti)) :
    RingHom.ker (stageModPFrobenius A t p n) = Ideal.span {stageX A t p n i} := by
  have heq : stageModPFrobenius A t p n =
      (stageRootModPFrobenius A t p n i hti).comp
        (Ideal.Quotient.mk (Ideal.span {stageX A t p n i})) := rfl
  rw [heq, RingHom.ker_comp_of_injective _ hf, Ideal.mk_ker]

/-- 有限段の射は、基底環からの作用をmod pの反復Frobeniusへ送る。 -/
theorem stageModPFrobenius_comp_algebraMap (n : ℕ) :
    (stageModPFrobenius A t p n).comp (algebraMap A (TowerStage A t p n)) =
      (iterateFrobenius (A ⧸ Ideal.span {(p : A)}) p n).comp
        (Ideal.Quotient.mk (Ideal.span {(p : A)})) := by
  ext a
  exact stageModPFrobenius_algebraMap A t p n a

/-- n乗根をm段で取ったとき、m段のFrobenius射による像はg^(p^(m-n))となる。
段と根の指数の差を、実際の像の冪として追跡する。 -/
theorem stageModPFrobenius_root_image [IsReduced (A ⧸ Ideal.span {(p : A)})]
    (n m : ℕ) (hnm : n ≤ m) (g : A) (z : TowerStage A t p m)
    (hz : z ^ (p ^ n) - algebraMap A (TowerStage A t p m) g ∈
      Ideal.span {(p : TowerStage A t p m)}) :
    stageModPFrobenius A t p m z =
      Ideal.Quotient.mk (Ideal.span {(p : A)}) g ^ (p ^ (m - n)) := by
  have hmap := Ideal.mem_map_of_mem (stageModPFrobenius A t p m) hz
  simp only [Ideal.map_span, Set.image_singleton, map_natCast, CharP.cast_eq_zero,
    Ideal.span_singleton_zero, Ideal.mem_bot, map_sub, map_pow,
    stageModPFrobenius_algebraMap] at hmap
  apply iterateFrobenius_inj (A ⧸ Ideal.span {(p : A)}) p n
  change stageModPFrobenius A t p m z ^ (p ^ n) =
    (Ideal.Quotient.mk (Ideal.span {(p : A)}) g ^ (p ^ (m - n))) ^ (p ^ n)
  rw [sub_eq_zero.mp hmap, ← pow_mul, ← pow_add, Nat.sub_add_cancel hnm]

/-- 基底極大イデアルの有限段への拡大は、mod p射によってFrobenius冪イデアルへ送られる。 -/
theorem stageModPFrobenius_map_base_maximalIdeal
    [IsLocalRing A] [IsLocalRing (A ⧸ Ideal.span {(p : A)})] (m : ℕ) :
    ((IsLocalRing.maximalIdeal A).map (algebraMap A (TowerStage A t p m))).map
      (stageModPFrobenius A t p m) =
        (IsLocalRing.maximalIdeal (A ⧸ Ideal.span {(p : A)})).map
          (iterateFrobenius (A ⧸ Ideal.span {(p : A)}) p m) := by
  rw [Ideal.map_map, stageModPFrobenius_comp_algebraMap, ← Ideal.map_map,
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]

/-- 根を零にし、根の代表元zを加えた有限段の関係式の、mod p射による実際の像。 -/
theorem stageModPFrobenius_map_root_relations
    [IsLocalRing A] [IsLocalRing (A ⧸ Ideal.span {(p : A)})]
    [IsReduced (A ⧸ Ideal.span {(p : A)})]
    (n m : ℕ) (hnm : n ≤ m) (i : Fin h) (hti : t i = (p : A))
    (g : A) (z : TowerStage A t p m)
    (hz : z ^ (p ^ n) - algebraMap A (TowerStage A t p m) g ∈
      Ideal.span {(p : TowerStage A t p m)}) :
    ((IsLocalRing.maximalIdeal A).map (algebraMap A (TowerStage A t p m)) ⊔
      Ideal.span {stageX A t p m i} ⊔ Ideal.span {z}).map (stageModPFrobenius A t p m) =
        (IsLocalRing.maximalIdeal (A ⧸ Ideal.span {(p : A)})).map
          (iterateFrobenius (A ⧸ Ideal.span {(p : A)}) p m) ⊔
            Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) g ^ (p ^ (m - n))} := by
  rw [Ideal.map_sup, Ideal.map_sup, stageModPFrobenius_map_base_maximalIdeal,
    Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
    stageModPFrobenius_stageX, hti]
  have hp : Ideal.Quotient.mk (Ideal.span {(p : A)}) (p : A) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [hp, Ideal.span_singleton_zero, sup_bot_eq,
    stageModPFrobenius_root_image A t p n m hnm g z hz]

/-- n段のp冪根をm段の冪として加えた関係式も、同じFrobenius商の関係式へ送られる。
源での冪の倍率は別のフィルトレーションで評価する。 -/
theorem stageModPFrobenius_map_root_power_relations
    [IsLocalRing A] [IsLocalRing (A ⧸ Ideal.span {(p : A)})]
    [IsReduced (A ⧸ Ideal.span {(p : A)})]
    (n m : ℕ) (hnm : n ≤ m) (i : Fin h) (hti : t i = (p : A))
    (g : A) (z : TowerStage A t p m)
    (hz : z ^ (p ^ n) - algebraMap A (TowerStage A t p m) g ∈
      Ideal.span {(p : TowerStage A t p m)}) :
    ((IsLocalRing.maximalIdeal A).map (algebraMap A (TowerStage A t p m)) ⊔
      Ideal.span {stageX A t p m i ^ (p ^ (m - n))} ⊔ Ideal.span {z}).map
        (stageModPFrobenius A t p m) =
          (IsLocalRing.maximalIdeal (A ⧸ Ideal.span {(p : A)})).map
            (iterateFrobenius (A ⧸ Ideal.span {(p : A)}) p m) ⊔
              Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) g ^ (p ^ (m - n))} := by
  rw [Ideal.map_sup, Ideal.map_sup, stageModPFrobenius_map_base_maximalIdeal,
    Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_pow,
    stageModPFrobenius_stageX, hti]
  have hp : Ideal.Quotient.mk (Ideal.span {(p : A)}) (p : A) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [hp, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero),
    Ideal.span_singleton_zero, sup_bot_eq, stageModPFrobenius_root_image A t p n m hnm g z hz]

end SerrePositivity.Section2
