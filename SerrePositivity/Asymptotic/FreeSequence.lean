module

public import Mathlib.Analysis.Asymptotics.Ring
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.LinearAlgebra.Pi

/-!
# ランクの増大を制御した自由加群列の加法圏

§4 の `E_S` の骨格を、ランク列 `r` と各段の標準自由加群 `S^(r n)` で表す。
対象に課す条件は通常の `atTop` における `r = O(s)` だけであり、射は任意の
線形写像の列である。射の係数に一様な有界性は課さない。
零対象と二項直和を具体的に構成し、共通有界な複体を作る加法圏を得る。
-/

@[expose] public section

universe u

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
