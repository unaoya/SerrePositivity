module

public import Mathlib.Analysis.Asymptotics.Ring
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # ランクの増大を制御した自由加群の列

## 概要

§4 の E_S の骨格として、ランクの列 r（r = O(s)）と各段の標準自由加群 S^(r n) による自由加群の列の加法圏 `FreeSequence R s` を作り（射は任意の線形写像の列）、標準基底の行列の係数に環準同型を当てた係数変更の加法関手を与える。

## 方針

射の係数に一様な有界性は課さない。ひねり（環の自己同型）も同じ係数変更で作る。

## 規約

一般の加群上のテンソル積との比較は `SequenceComplex` で行う。

## 使われ方

Asymptotic の全体。
-/

@[expose] public noncomputable section

universe u

section FreeSequencePart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits Filter Asymptotics

/-- 正規化列 `s` に対してランクが `O(s)` となる標準自由加群列。 -/
def FreeSequence (_R : Type u) (s : ℕ → ℕ) :=
  {r : ℕ → ℕ // (fun n ↦ (r n : ℝ)) =O[atTop] (fun n ↦ (s n : ℝ))}

namespace FreeSequence

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 各段の自由加群の基底の個数。 -/
def rank (X : FreeSequence R s) : ℕ → ℕ := X.1

omit [CommRing R] in
/-- 対象のランク列は指定された増大度を満たす。 -/
lemma rank_isBigO (X : FreeSequence R s) :
    (fun n ↦ (X.rank n : ℝ)) =O[atTop] (fun n ↦ (s n : ℝ)) := X.2

/-- 自由加群列の射は、各段の線形写像の任意の列である。 -/
instance : Category (FreeSequence R s) where
  Hom X Y := ∀ n, (Fin (X.rank n) → R) →ₗ[R] (Fin (Y.rank n) → R)
  id X _ := LinearMap.id
  comp f g n := (g n).comp (f n)

/-- 射の加法と合成は各段で計算する。 -/
instance : Preadditive (FreeSequence R s) where
  homGroup X Y := inferInstanceAs
    (AddCommGroup (∀ n, (Fin (X.rank n) → R) →ₗ[R] (Fin (Y.rank n) → R)))
  add_comp _ _ _ f g h := by
    funext n
    apply LinearMap.ext
    intro x
    exact (h n).map_add (f n x) (g n x)
  comp_add _ _ _ f g h := by
    funext n
    apply LinearMap.ext
    intro x
    rfl

/-- 列の射の一致は各段の線形写像で判定できる。 -/
@[ext] lemma hom_ext {X Y : FreeSequence R s} {f g : X ⟶ Y}
    (h : ∀ n, f n = g n) : f = g := funext h

/-- 第 `n` 項を取り出す加法関手。 -/
def evaluation (n : ℕ) : FreeSequence R s ⥤ ModuleCat.{u} R where
  obj X := ModuleCat.of R (Fin (X.rank n) → R)
  map f := ModuleCat.ofHom (f n)

instance (n : ℕ) : (evaluation (R := R) (s := s) n).Additive where
  map_add := by intros; rfl

/-- すべてのランクが零の列。 -/
def zero : FreeSequence R s := ⟨fun _ ↦ 0, by simpa using (isBigO_zero ..)⟩

/-- ランク零の列は零対象である。 -/
lemma zero_isZero : IsZero (zero : FreeSequence R s) := by
  apply (IsZero.iff_id_eq_zero _).2
  ext n x i
  exact Fin.elim0 i

instance : HasZeroObject (FreeSequence R s) := ⟨⟨zero, zero_isZero⟩⟩

/-- 二つのランク列の和が与える自由加群列。 -/
def sum (X Y : FreeSequence R s) : FreeSequence R s :=
  ⟨fun n ↦ X.rank n + Y.rank n, by
    simpa only [Nat.cast_add] using X.rank_isBigO.add Y.rank_isBigO⟩

/-- 標準自由加群の添字の分割による直和分解。 -/
noncomputable def sumEquiv (X Y : FreeSequence R s) (n : ℕ) :
    (Fin ((sum X Y).rank n) → R) ≃ₗ[R]
      (Fin (X.rank n) → R) × (Fin (Y.rank n) → R) :=
  (LinearEquiv.funCongrLeft R R finSumFinEquiv) ≪≫ₗ
    LinearEquiv.sumArrowLequivProdArrow _ _ R R

/-- ランクの和で表される二項直和の bicone。 -/
noncomputable def sumBicone (X Y : FreeSequence R s) : BinaryBicone X Y where
  pt := sum X Y
  fst n := (LinearMap.fst R _ _).comp (sumEquiv X Y n).toLinearMap
  snd n := (LinearMap.snd R _ _).comp (sumEquiv X Y n).toLinearMap
  inl n := (sumEquiv X Y n).symm.toLinearMap.comp (LinearMap.inl R _ _)
  inr n := (sumEquiv X Y n).symm.toLinearMap.comp (LinearMap.inr R _ _)
  inl_fst := by
    funext n
    apply LinearMap.ext
    intro x
    exact congrArg Prod.fst ((sumEquiv X Y n).apply_symm_apply (x, 0))
  inl_snd := by
    funext n
    apply LinearMap.ext
    intro x
    exact congrArg Prod.snd ((sumEquiv X Y n).apply_symm_apply (x, 0))
  inr_fst := by
    funext n
    apply LinearMap.ext
    intro x
    exact congrArg Prod.fst ((sumEquiv X Y n).apply_symm_apply (0, x))
  inr_snd := by
    funext n
    apply LinearMap.ext
    intro x
    exact congrArg Prod.snd ((sumEquiv X Y n).apply_symm_apply (0, x))

/-- ランクの和の bicone は実際に二項直和である。 -/
lemma sumBicone_total (X Y : FreeSequence R s) :
    (sumBicone X Y).fst ≫ (sumBicone X Y).inl +
      (sumBicone X Y).snd ≫ (sumBicone X Y).inr = 𝟙 _ := by
  apply hom_ext
  intro n
  apply LinearMap.ext
  intro x
  change (sumEquiv X Y n).symm ((sumEquiv X Y n x).1, 0) +
    (sumEquiv X Y n).symm (0, (sumEquiv X Y n x).2) = x
  rw [← map_add]
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using
    (sumEquiv X Y n).symm_apply_apply x

noncomputable instance (X Y : FreeSequence R s) : HasBinaryBiproduct X Y :=
  hasBinaryBiproduct_of_total (sumBicone X Y) (sumBicone_total X Y)

noncomputable instance : HasBinaryBiproducts (FreeSequence R s) := ⟨inferInstance⟩

noncomputable instance : HasFiniteBiproducts (FreeSequence R s) := by
  let := hasFiniteProducts_of_has_binary_and_terminal (C := FreeSequence R s)
  exact HasFiniteBiproducts.of_hasFiniteProducts

/-- 論文の標準列 `U_R = (R^(s n))`。 -/
def generator (R : Type u) (s : ℕ → ℕ) : FreeSequence R s :=
  ⟨s, isBigO_refl _ _⟩

end FreeSequence

end SerrePositivity.Asymptotic

end FreeSequencePart

section FreeSequenceBaseChangePart

namespace SerrePositivity.Asymptotic.FreeSequence

open CategoryTheory Filter Asymptotics

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {s : ℕ → ℕ}

/-- 標準自由加群間の線形写像の行列に環準同型を施す。 -/
noncomputable def changeMatrix (φ : R →+* S) {a b : ℕ}
    (f : (Fin a → R) →ₗ[R] (Fin b → R)) :
    (Fin a → S) →ₗ[S] (Fin b → S) :=
  Matrix.toLin' ((LinearMap.toMatrix' f).map φ)

/-- 行列の係数変更は恒等写像を保つ。 -/
@[simp] lemma changeMatrix_id (φ : R →+* S) (a : ℕ) :
    changeMatrix φ (LinearMap.id : (Fin a → R) →ₗ[R] (Fin a → R)) = LinearMap.id := by
  simp [changeMatrix, LinearMap.toMatrix'_id, Matrix.map_one _ φ.map_zero φ.map_one]

/-- 行列の係数変更は合成を保つ。 -/
lemma changeMatrix_comp (φ : R →+* S) {a b c : ℕ}
    (f : (Fin a → R) →ₗ[R] (Fin b → R)) (g : (Fin b → R) →ₗ[R] (Fin c → R)) :
    changeMatrix φ (g.comp f) = (changeMatrix φ g).comp (changeMatrix φ f) := by
  simp [changeMatrix, LinearMap.toMatrix'_comp, Matrix.map_mul, Matrix.toLin'_mul]

/-- 行列の係数変更は加法を保つ。 -/
lemma changeMatrix_add (φ : R →+* S) {a b : ℕ}
    (f g : (Fin a → R) →ₗ[R] (Fin b → R)) :
    changeMatrix φ (f + g) = changeMatrix φ f + changeMatrix φ g := by
  simp [changeMatrix, Matrix.map_add _ φ.map_add]

/-- 環準同型による自由加群列の係数変更関手。 -/
noncomputable def changeRing (φ : R →+* S) : FreeSequence R s ⥤ FreeSequence S s where
  obj X := ⟨X.rank, X.rank_isBigO⟩
  map f n := changeMatrix φ (f n)
  map_id X := funext fun n ↦ changeMatrix_id φ (X.rank n)
  map_comp f g := funext fun n ↦ changeMatrix_comp φ (f n) (g n)

instance (φ : R →+* S) : (changeRing (s := s) φ).Additive where
  map_add {X Y} f g := by
    apply hom_ext
    intro n
    change changeMatrix φ (f n + g n) = changeMatrix φ (f n) + changeMatrix φ (g n)
    exact changeMatrix_add φ (f n) (g n)

/-- 係数変更は各段の基底の個数を保つ。 -/
@[simp] lemma changeRing_rank (φ : R →+* S) (X : FreeSequence R s) :
    ((changeRing φ).obj X).rank = X.rank := rfl

/-- ランクが `o(s)` の自由列は、係数変更後も同じ条件を満たす。 -/
lemma changeRing_rank_isLittleO (φ : R →+* S) (X : FreeSequence R s)
    (hX : (fun n ↦ (X.rank n : ℝ)) =o[atTop] (fun n ↦ (s n : ℝ))) :
    (fun n ↦ (((changeRing φ).obj X).rank n : ℝ)) =o[atTop] (fun n ↦ (s n : ℝ)) := hX

end SerrePositivity.Asymptotic.FreeSequence

end FreeSequenceBaseChangePart
