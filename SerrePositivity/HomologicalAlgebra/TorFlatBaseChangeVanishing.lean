module

public import SerrePositivity.HomologicalAlgebra.FlatBaseChange
public import SerrePositivity.HomologicalAlgebra.BaseChangeEquivalence
public import SerrePositivity.HomologicalAlgebra.LocalFlatnessCriterion
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Quotient

/-! # 平坦な係数拡大と Tor の消滅

## 概要

`R → S` が平坦、`T` が `S` 代数（したがって `R` 代数）、`D` が `R` 加群のとき、
`Tor_n^R(T, D) = 0` なら `Tor_n^S(T, S ⊗_R D) = 0`。

## 方針

`D` の射影分解 `K` を `S` へ係数拡大すると、平坦性からホモロジーが保たれるので
`S ⊗_R D` の射影分解になる（`isResolutionOf_baseChange_of_flat`）。
`Tor^S(T, S ⊗_R D)` はこの分解をさらに `T` へ係数拡大した複体のホモロジーで、
二段階の係数拡大は `R → T` への一段階の係数拡大と同型。そのホモロジーは `Tor^R(T, D)`。

## 使われ方

解説の付録 A（「引用している結果」の対角線論法の段落）の工程（平坦な底変換での Tor の比較）。
対角線の環 `S` で `Tor_{>0}^S(S/(δ), S ⊗_R D) = 0` を、`S/(δ) ≅ R` が `R` 上自由であることから導く。
-/

@[expose] public section

universe u

namespace SerrePositivity

open CategoryTheory Limits TensorProduct

set_option backward.isDefEq.respectTransparency false

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

/-- **平坦な係数拡大と分解**：射影分解を平坦な係数拡大で移すと、係数拡大した加群の射影分解になる。 -/
noncomputable def isResolutionOf_baseChange_of_flat (D : Type u) [AddCommGroup D] [Module R D]
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsResolutionOf K (ModuleCat.of R D)) :
    IsResolutionOf (baseChange (algebraMap R S) K) (ModuleCat.of S (S ⊗[R] D)) := by
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap R S)
  let : F.PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (ModuleCat.extendRestrictScalarsAdj (algebraMap R S))
  refine
    { isZero_X := fun i hi ↦ baseChange_isZero_X_of_pos _ K hK.isZero_X i hi
      projective := fun i ↦ by
        have := hK.projective i
        change Projective (F.obj (K.X i))
        infer_instance
      isZero_homology := fun i hi ↦ ?_
      homologyZeroIso := ?_ }
  · have hz := hK.isZero_homology i hi
    have : Subsingleton (K.homology i) := ModuleCat.subsingleton_of_isZero hz
    exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton (ModuleCat.of S (S ⊗[R] K.homology i)))
      (flatBaseChangeHomologyEquiv R S K i).toModuleIso
  · exact ((flatBaseChangeHomologyEquiv R S K 0).trans
      (LinearEquiv.baseChange R S _ _ hK.homologyZeroIso.toLinearEquiv)).toModuleIso

variable (T : Type u) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- **Tor の消滅の移送**：`R → S` が平坦なら、`Tor_n^R(T, D) = 0` から `Tor_n^S(T, S ⊗_R D) = 0`。 -/
theorem torModule_baseChange_subsingleton (D : Type u) [AddCommGroup D] [Module R D] (n : ℕ)
    (h : Subsingleton (TorModule R n T D)) : Subsingleton (TorModule S n T (S ⊗[R] D)) := by
  let P := projectiveResolution (ModuleCat.of R D)
  have hK := isResolutionOf_extRes P
  have hK' := isResolutionOf_baseChange_of_flat R S D hK
  let e₁ := ordinaryTorIso (R := S) (T := T) (S ⊗[R] D) _ hK' n
  let e₂ := ordinaryTorIso (R := R) (T := T) D _ hK n
  have : Subsingleton (TorModule R n T D) := h
  have h₂ : Subsingleton ((baseChange (algebraMap R T) (extRes P)).homology (-(n : ℤ))) :=
    e₂.injective.subsingleton
  have hcomp : (algebraMap S T).comp (algebraMap R S) = algebraMap R T :=
    (IsScalarTower.algebraMap_eq R S T).symm
  have e₃ : (baseChange (algebraMap S T) (baseChange (algebraMap R S) (extRes P))).homology
      (-(n : ℤ)) ≅ (baseChange (algebraMap R T) (extRes P)).homology (-(n : ℤ)) := by
    rw [← hcomp]
    exact (HomologicalComplex.homologyFunctor _ _ (-(n : ℤ))).mapIso
      (baseChangeCompIso (algebraMap R S) (algebraMap S T) (extRes P))
  have h₃ : Subsingleton ((baseChange (algebraMap S T)
      (baseChange (algebraMap R S) (extRes P))).homology (-(n : ℤ))) :=
    e₃.toLinearEquiv.injective.subsingleton
  have h₄ : Subsingleton ((ModuleCat.restrictScalars (algebraMap S T)).obj
      ((baseChange (algebraMap S T) (baseChange (algebraMap R S) (extRes P))).homology
        (-(n : ℤ)))) := h₃
  exact e₁.symm.injective.subsingleton

/-- **商加群での形**：環準同型 `φ : R → S` が平坦で、`S` 代数 `T` が `R` 上平坦なら、
任意のイデアル `P ⊆ R` について `Tor_{n+1}^S(T, S/PS) = 0`。代数構造を引数の環準同型から作るので、
`S` に別の `R` 代数構造があっても使える。 -/
theorem torModule_quotient_map_subsingleton {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : φ.Flat) (T : Type u) [CommRing T] [Algebra S T]
    (hT : ((algebraMap S T).comp φ).Flat) (P : Ideal R) (n : ℕ) :
    Subsingleton (TorModule S (n + 1) T (S ⧸ P.map φ)) := by
  let : Algebra R S := φ.toAlgebra
  let : Algebra R T := ((algebraMap S T).comp φ).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Flat R S := hφ
  have : Module.Flat R T := hT
  have h := torModule_baseChange_subsingleton R S T (R ⧸ P) (n + 1)
    (torModule_subsingleton_of_flat (R := R) T (R ⧸ P) n)
  exact torModule_subsingleton_of_linearEquiv T
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S P).toLinearEquiv.symm (n + 1) h

end SerrePositivity
