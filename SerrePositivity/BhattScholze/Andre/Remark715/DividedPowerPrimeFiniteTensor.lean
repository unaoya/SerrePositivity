module

public import SerrePositivity.BhattScholze.Andre.Remark715.DividedPowerPrimeTensor
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.Flat.Basic

/-!
# André E1・E2：有限切断テンソル段の分冪評価

## 概要

切断多項式環 A[X]/(Xᵖ) の有限反復テンソル積を一元分冪代数へ単射に写す。
BS Rem 7.15(1)（著者版 p.62）の可算切断表示の有限段である。

## 方針

最初の切断変数を分けるテンソル同型と、モニック商の自由性による
テンソル化の単射性保存を反復する。

## 規約

係数環 A は可換環、p は素数で A 内で零とする。零環も含む。
有限段の束には標準の CommAlgCat を用い、係数環作用を保持する。

## 使われ方

可算多項式の有限変数支持に制限した評価の単射性へ接続する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open scoped TensorProduct
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
local notation "DA" => DividedPowerAlgebra A A
local notation "C" => AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)

/-- 概要：分冪代数への単射を切断変数一つを加えた単射へ拡張する。
方針：モニック商の自由性によるテンソル化と、次数シフトのテンソル分解を合成する。
規約：入力代数の平坦性を仮定しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の有限切断段の帰納。 -/
theorem dividedPowerPrimeTensorMap_comp_injective (hp : (p : A) = 0)
    {B : Type u} [CommRing B] [Algebra A B]
    (f : B →ₐ[A] DA) (hf : Function.Injective f) :
    Function.Injective ((dividedPowerPrimeTensorMap p hp).comp
      (Algebra.TensorProduct.map (AlgHom.id A C) f)) := by
  let : Module.Free A C := (Polynomial.monic_X.pow p).free_adjoinRoot
  have he : (Algebra.TensorProduct.map (AlgHom.id A C) f).toLinearMap =
      f.toLinearMap.lTensor C := by
    ext c b
    rfl
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id A C) f) := by
    change Function.Injective (Algebra.TensorProduct.map (AlgHom.id A C) f).toLinearMap
    rw [he]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hf
  exact (dividedPowerPrimeTensorMap_bijective p hp).injective.comp hinj

omit [Fact p.Prime] in
/-- 概要：n 個の切断変数を持つ有限反復テンソル段を係数代数として束ねる。
方針：零段を A、次段を A[X]/(Xᵖ) と前段のテンソル積にする。
規約：この定義には素数性や標数の仮定は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の有限変数支持の入れ物。 -/
def dividedPowerPrimeTensorStage : ℕ → CommAlgCat.{u} A
  | 0 => CommAlgCat.of A A
  | n + 1 => CommAlgCat.of A (C ⊗[A] dividedPowerPrimeTensorStage n)

/-- 概要：有限テンソル段から一元分冪代数への標準評価射。
方針：前段の評価をテンソル化し、最初の切断変数と次数シフトの積に送る。
規約：n 番目の変数に対応する次数は p の n 乗である。
使われ方：BS Rem 7.15(1)（著者版 p.62）の有限切断評価。 -/
def dividedPowerPrimeTensorStageEval (hp : (p : A) = 0) :
    (n : ℕ) → dividedPowerPrimeTensorStage (A := A) p n →ₐ[A] DA
  | 0 => Algebra.ofId A DA
  | n + 1 => (dividedPowerPrimeTensorMap p hp).comp
      (Algebra.TensorProduct.map (AlgHom.id A C) (dividedPowerPrimeTensorStageEval hp n))

/-- 概要：各有限テンソル段の標準分冪評価は単射。
方針：零段では標準分冪基底の係数埋込、次段では切断テンソル化の単射性保存を使う。
規約：係数環の非零性を要求しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の可算表示を有限支持へ制限する。 -/
theorem dividedPowerPrimeTensorStageEval_injective (hp : (p : A) = 0) (n : ℕ) :
    Function.Injective (dividedPowerPrimeTensorStageEval (A := A) p hp n) := by
  induction n with
  | zero =>
    change Function.Injective (algebraMap A DA)
    intro a b hab
    have hone : (1 : DA) = rankOneDPAnyBasis A 0 := by
      rw [rankOneDPAnyBasis_apply, DividedPowerAlgebra.dp_zero]
    have h := congrArg (fun x : DA => (rankOneDPAnyBasis A).repr x 0) hab
    simpa [Algebra.algebraMap_eq_smul_one, hone] using h
  | succ n ih =>
    exact dividedPowerPrimeTensorMap_comp_injective p hp _ ih


omit [Fact p.Prime] in
/-- 概要：有限テンソル段の i 番目の切断変数。
方針：最初の変数は左因子の根、後続は右因子の変数として再帰する。
規約：番号は Fin n であり、零段に変数はない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の多項式変数との照合。 -/
def dividedPowerPrimeTensorStageRoot :
    (n : ℕ) → Fin n → dividedPowerPrimeTensorStage (A := A) p n
  | 0, i => Fin.elim0 i
  | n + 1, i => Fin.cases
      (AdjoinRoot.root ((Polynomial.X : Polynomial A) ^ p) ⊗ₜ[A] 1)
      (fun j => 1 ⊗ₜ[A] dividedPowerPrimeTensorStageRoot n j) i

omit [Fact p.Prime] in
/-- 概要：有限テンソル段の変数は p 乗が零。
方針：左因子の根の関係式と右因子の帰納仮定を純テンソルの冪へ適用する。
規約：この消滅自体には標数や素数性は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の切断多項式商からの射の構成。 -/
theorem dividedPowerPrimeTensorStageRoot_pow (n : ℕ) (i : Fin n) :
    dividedPowerPrimeTensorStageRoot (A := A) p n i ^ p = 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change (AdjoinRoot.root ((Polynomial.X : Polynomial A) ^ p) ⊗ₜ[A]
        (1 : dividedPowerPrimeTensorStage (A := A) p n)) ^ p = 0
      rw [Algebra.TensorProduct.tmul_pow, one_pow]
      have hroot : AdjoinRoot.root ((Polynomial.X : Polynomial A) ^ p) ^ p = 0 := by
        simpa only [Polynomial.eval₂_pow, Polynomial.eval₂_X] using
          AdjoinRoot.eval₂_root ((Polynomial.X : Polynomial A) ^ p)
      rw [hroot, TensorProduct.zero_tmul]
    · change ((1 : C) ⊗ₜ[A] dividedPowerPrimeTensorStageRoot p n j) ^ p = 0
      rw [Algebra.TensorProduct.tmul_pow, one_pow, ih j, TensorProduct.tmul_zero]

/-- 概要：有限段の i 番目の変数の分冪評価は γₚⁱ。
方針：最初の変数の評価と、次数シフトによる添字の p 倍を帰納する。
規約：切断変数の番号をそのまま素数冪の指数に使う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の標準多項式評価との比較。 -/
theorem dividedPowerPrimeTensorStageEval_root (hp : (p : A) = 0) (n : ℕ) (i : Fin n) :
    dividedPowerPrimeTensorStageEval p hp n (dividedPowerPrimeTensorStageRoot p n i) =
      DividedPowerAlgebra.dp A (p ^ (i : ℕ)) (1 : A) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change dividedPowerPrimeTensorMap p hp
        (Algebra.TensorProduct.map (AlgHom.id A C) (dividedPowerPrimeTensorStageEval p hp n)
          (AdjoinRoot.root ((Polynomial.X : Polynomial A) ^ p) ⊗ₜ[A] 1)) = _
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one,
        dividedPowerPrimeTensorMap_tmul, rankOneDPTruncatedMap_root, mul_one,
        Fin.val_zero, pow_zero]
    · change dividedPowerPrimeTensorMap p hp
        (Algebra.TensorProduct.map (AlgHom.id A C) (dividedPowerPrimeTensorStageEval p hp n)
          (1 ⊗ₜ[A] dividedPowerPrimeTensorStageRoot p n j)) = _
      simp only [Algebra.TensorProduct.map_tmul, ih,
        dividedPowerPrimeTensorMap_tmul, map_one, one_mul, dividedPowerPrimeShift_dp,
        Fin.val_succ, pow_succ']

end SerrePositivity.BhattScholze.Andre
