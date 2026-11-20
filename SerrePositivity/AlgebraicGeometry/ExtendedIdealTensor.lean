module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.Module

/-!
概要：KST §5、Stacks 0810 の局所自由性の準備となる拡大イデアルのテンソル写像。
方針：基礎環のイデアルの元を代数に送り、代数上のテンソル積へ降ろす。
規約：二つの環上の加群構造とスカラー塔を明示する。
使われ方：基礎環上の平坦性を拡大イデアルに関する単射性へ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/--
概要：基礎環のイデアルから拡大イデアルへの実際の基礎環線形写像。
方針：係数写像の終域を拡大イデアルへ制限する。
規約：KST §5、Stacks 0810 の局所自由性の準備。
使われ方：二つの環上のテンソル積を比較する。
-/
def idealExtensionLinearMap (I : Ideal R) : I →ₗ[R] I.map (algebraMap R S) :=
  ((Algebra.linearMap R S).comp I.subtype).codRestrict
    ((I.map (algebraMap R S)).restrictScalars R)
    (fun x => Ideal.mem_map_of_mem _ x.property)

/--
概要：基礎環のイデアルのテンソル積から拡大イデアルの代数上のテンソル積への実比較写像。
方針：代数上のテンソル積の双線形写像を基礎環へ制限して普遍性を使う。
規約：KST §5、Stacks 0810 の局所自由性の準備、環の平坦性は仮定しない。
使われ方：基礎環上の平坦性から拡大イデアルの作用写像の単射性を導く。
-/
def idealExtensionTensorMap (I : Ideal R) :
    (I ⊗[R] M) →ₗ[R] ((I.map (algebraMap R S)) ⊗[S] M) :=
  TensorProduct.lift
    (((TensorProduct.mk S (I.map (algebraMap R S)) M).restrictScalars₁₂ R R).comp
      (idealExtensionLinearMap (S := S) I))

/--
概要：拡大イデアルのテンソル比較写像の純テンソル上の値。
方針：テンソル積の lift の定義を使う。
規約：KST §5、Stacks 0810 の局所自由性の準備。
使われ方：全射性と作用写像との可換性の計算。
-/
theorem idealExtensionTensorMap_tmul (I : Ideal R) (i : I) (m : M) :
    idealExtensionTensorMap (S := S) I (i ⊗ₜ[R] m) =
      idealExtensionLinearMap (S := S) I i ⊗ₜ[S] m := rfl

/--
概要：拡大イデアルのテンソル比較写像は全射。
方針：拡大イデアルの生成元の帰納法で代数の係数を加群側へ移し、テンソル積の帰納法を使う。
規約：KST §5、Stacks 0810 の局所自由性の準備、Noether 性や平坦性は不要。
使われ方：基礎環のイデアルから代数の拡大イデアルへ作用の単射性を移す。
-/
theorem idealExtensionTensorMap_surjective (I : Ideal R) :
    Function.Surjective (idealExtensionTensorMap (S := S) (M := M) I) := by
  have hgens : ∀ (s : S) (hs : s ∈ I.map (algebraMap R S)) (m : M),
      ∃ z : I ⊗[R] M, idealExtensionTensorMap (S := S) I z = ⟨s, hs⟩ ⊗ₜ[S] m := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨i, hi, rfl⟩ := hs
      intro m
      exact ⟨(⟨i, hi⟩ : I) ⊗ₜ[R] m, rfl⟩
    | zero =>
      intro m
      exact ⟨0, by change _ = (0 : I.map (algebraMap R S)) ⊗ₜ[S] m; simp⟩
    | add s t hs ht ihs iht =>
      intro m
      obtain ⟨x, hx⟩ := ihs m
      obtain ⟨y, hy⟩ := iht m
      refine ⟨x + y, ?_⟩
      change idealExtensionTensorMap (S := S) I (x + y) =
        ((⟨s, hs⟩ : I.map (algebraMap R S)) + ⟨t, ht⟩) ⊗ₜ[S] m
      rw [map_add, hx, hy, TensorProduct.add_tmul]
    | smul a s hs ih =>
      intro m
      obtain ⟨x, hx⟩ := ih (a • m)
      refine ⟨x, ?_⟩
      change idealExtensionTensorMap (S := S) I x =
        (a • (⟨s, hs⟩ : I.map (algebraMap R S))) ⊗ₜ[S] m
      rwa [TensorProduct.smul_tmul]
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul i m => exact hgens i.val i.property m
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb]⟩

/--
概要：イデアルと加群のテンソル積から加群への作用写像。
方針：イデアルの包含をテンソル化し、環とのテンソル積の単位同型を合成する。
規約：KST §5、Stacks 0810 の局所自由性の準備。
使われ方：平坦性から得られる単射性を異なる環の間で比較する。
-/
def idealTensorAction (I : Ideal R) : I ⊗[R] M →ₗ[R] M :=
  (TensorProduct.lid R M).toLinearMap.comp (I.subtype.rTensor M)

/--
概要：拡大イデアルへのテンソル比較は作用写像と可換。
方針：純テンソル上で計算し、スカラー塔の等式を使う。
規約：KST §5、Stacks 0810、基礎環上の線形写像として比較する。
使われ方：基礎環上の平坦性から拡大イデアルの作用の単射性を得る。
-/
theorem idealExtensionTensorMap_action (I : Ideal R) :
    ((idealTensorAction (R := S) (M := M) (I.map (algebraMap R S))).restrictScalars R).comp
      (idealExtensionTensorMap (S := S) I) = idealTensorAction (M := M) I := by
  ext i m
  change (TensorProduct.lid S M)
      (((I.map (algebraMap R S)).subtype.rTensor M)
        (idealExtensionLinearMap (S := S) I i ⊗ₜ[S] m)) =
    (TensorProduct.lid R M) ((I.subtype.rTensor M) (i ⊗ₜ[R] m))
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
  change algebraMap R S (i : R) • m = (i : R) • m
  exact algebraMap_smul S (i : R) m

/--
概要：基礎環上平坦な加群では拡大イデアルの作用写像が単射。
方針：比較写像の全射性で元を持ち上げ、作用の可換性と基礎環上の平坦性を使う。
規約：KST §5、Stacks 0810、代数自身の平坦性は不要。
使われ方：極大イデアルが拡大される局所環での有限表示加群の自由性判定。
-/
theorem extendedIdeal_rTensor_injective [Module.Flat R M] (I : Ideal R) :
    Function.Injective ((I.map (algebraMap R S)).subtype.rTensor M) := by
  have hinj : Function.Injective (idealTensorAction (M := M) I) :=
    (TensorProduct.lid R M).injective.comp
      (Module.Flat.rTensor_preserves_injective_linearMap I.subtype Subtype.val_injective)
  intro x y hxy
  obtain ⟨a, rfl⟩ := idealExtensionTensorMap_surjective (S := S) (M := M) I x
  obtain ⟨b, rfl⟩ := idealExtensionTensorMap_surjective (S := S) (M := M) I y
  apply congrArg (idealExtensionTensorMap (S := S) (M := M) I)
  apply hinj
  have h := congrArg (TensorProduct.lid S M) hxy
  change idealTensorAction (R := S) (I.map (algebraMap R S))
      (idealExtensionTensorMap (S := S) I a) =
    idealTensorAction (R := S) (I.map (algebraMap R S))
      (idealExtensionTensorMap (S := S) I b) at h
  change (((idealTensorAction (R := S) (M := M)
      (I.map (algebraMap R S))).restrictScalars R).comp
      (idealExtensionTensorMap (S := S) I)) a =
    (((idealTensorAction (R := S) (M := M)
      (I.map (algebraMap R S))).restrictScalars R).comp
      (idealExtensionTensorMap (S := S) I)) b at h
  rw [idealExtensionTensorMap_action] at h
  exact h

/--
概要：極大イデアルが基礎環のイデアルの拡大なら有限表示の平坦加群は自由。
方針：拡大イデアルに対するテンソル包含の単射性を局所自由性判定に使う。
規約：KST §5、Stacks 0810、基礎環には局所環の仮定を置かない。
使われ方：拡大素イデアルで局所化した加群の自由性を直接得る。
-/
theorem free_of_flat_of_maximalIdeal_eq_extendedIdeal [IsLocalRing S]
    [Module.Flat R M] [Module.FinitePresentation S M] (I : Ideal R)
    (hmax : IsLocalRing.maximalIdeal S = I.map (algebraMap R S)) : Module.Free S M := by
  apply Module.free_of_maximalIdeal_rTensor_injective
  rw [hmax]
  exact extendedIdeal_rTensor_injective (M := M) I

/--
概要：極大イデアルが拡大される局所環上では基礎環上平坦な有限表示加群は自由。
方針：拡大極大イデアルのテンソル包含の単射性を既存の局所自由性判定へ渡す。
規約：KST §5、Stacks 0810、二つの局所環と両立する加群作用を使う。
使われ方：幾何学的整なファイバーの一般点での局所自由性を確かめる。
-/
theorem free_of_flat_of_maximalIdeal_eq_map [IsLocalRing R] [IsLocalRing S]
    [Module.Flat R M] [Module.FinitePresentation S M]
    (hmax : IsLocalRing.maximalIdeal S =
      (IsLocalRing.maximalIdeal R).map (algebraMap R S)) : Module.Free S M := by
  exact free_of_flat_of_maximalIdeal_eq_extendedIdeal (IsLocalRing.maximalIdeal R) hmax

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
