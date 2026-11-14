module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDTermPointwiseCoefficients
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCech
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseTensorExt
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDTermPointwiseCoefficients
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDTermCompletedTensor
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Envelopes.PDModelBaseChange
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.TensorCompletionUnit
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseBaseChange

/-!
# 小さい分冪項の完備係数比較と構造射

## 概要
各項の完備係数比較を余単体の構造射に合わせる。

## 方針
完備な標的への線形射は純テンソルの単位上で決まることを使い、係数変更の厳密な自然性へ戻す。

## 規約
小さい分冪模型の実際の構造射を使う。

## 使われ方
BS 著者版 Theorem 6.4 の交代余面複体上の比較。
-/

public noncomputable section
open CategoryTheory
open scoped TensorProduct Simplicial ChangeOfRings
open SerrePositivity.DerivedCompletion
universe u
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) (k l : Type u) [CommRing k] [CommRing l] [Algebra k l] (r : ℕ)

/-- 純テンソルの完備化単位上の比較は、左係数倍を保った係数変更である。 -/
theorem pdTermPointwiseCoefficientIso_unit_smul (n : ℕ) (b : l) (x : pdTerm p k r n) :
    (pdTermPointwiseCoefficientIso p k l r n).hom
      (((moduleCompletionH0Unit l (p : l)).app
        ((ModuleCat.extendScalars (algebraMap k l)).obj (ModuleCat.of k (pdTerm p k r n))))
          (b ⊗ₜ[k,algebraMap k l] x)) =
      b • pdTermCoefficientRingHom p k l r n x := by
  let e := pdTermCompletedTensorAlgEquiv p k l r n
  change e ((pCompletedScalarExtensionTensorIso p k l (pdTerm p k r n)).hom _) = _
  rw [pCompletedScalarExtensionTensorIso_unit]
  let L : l ⊗[k] pdTerm p k r n →ₗ[l] pdTerm p l r n :=
    e.toLinearMap.comp
      (TensorCompletionUnit.unitAlg p l (l ⊗[k] pdTerm p k r n)).toLinearMap
  have hb : (b ⊗ₜ[k] x : l ⊗[k] pdTerm p k r n) = b • ((1 : l) ⊗ₜ[k] x) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  change L (b ⊗ₜ[k] x) = _
  rw [hb, L.map_smul]
  exact congrArg (b • ·) (pdTermCompletedTensorAlgEquiv_coefficient p k l r n x)

/-- 小さい完備分冪模型の構造射を、係数線形な代数射として読む。 -/
def pdTermStructureAlgHom {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    pdTerm p k r m →ₐ[k] pdTerm p k r n := by
  refine ⟨((pdModel p k r).map θ).right.hom, ?_⟩
  intro a
  exact ConcreteCategory.congr_hom (Under.w ((pdModel p k r).map θ)) a

/-- 各項の完備係数比較は、すべての余単体構造射と厳密に可換。 -/
theorem pdTermPointwiseCoefficientIso_naturality {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (pCompletedScalarExtensionFunctor p (algebraMap k l)).map
        (ModuleCat.ofHom (pdTermStructureAlgHom p k r θ).toLinearMap) ≫
      (pdTermPointwiseCoefficientIso p k l r n).hom =
    (pdTermPointwiseCoefficientIso p k l r m).hom ≫
      ModuleCat.ofHom (pdTermStructureAlgHom p l r θ).toLinearMap := by
  apply pCompletedScalarExtension_hom_ext p k l (pdTerm p k r m)
    (ModuleCat.of l (pdTerm p l r n))
    (completedRing_isModuleComplete l p (A := pdRaw l r n))
  intro b x
  change (pdTermPointwiseCoefficientIso p k l r n).hom
      ((pCompletedScalarExtensionFunctor p (algebraMap k l)).map
        (ModuleCat.ofHom (pdTermStructureAlgHom p k r θ).toLinearMap) _) =
    pdTermStructureAlgHom p l r θ ((pdTermPointwiseCoefficientIso p k l r m).hom _)
  rw [pCompletedScalarExtension_map_unit, pdTermPointwiseCoefficientIso_unit_smul,
    pdTermPointwiseCoefficientIso_unit_smul, map_smul]
  congr 1
  have hn := congrArg (fun t => Under.Hom.right t)
    ((pdModelBaseChange p k l r).naturality θ)
  exact ConcreteCategory.congr_hom hn x

/-- 小さい分冪 Čech 模型の各項の完備係数拡大は、余単体的加群として係数変更先と同型。 -/
def pdCechPointwiseCoefficientIso :
    SerrePositivity.Cosimplicial.toModules k (pdCechRings p k r) (pdCechBase p k r) ⋙
        pCompletedScalarExtensionFunctor p (algebraMap k l) ≅
      SerrePositivity.Cosimplicial.toModules l (pdCechRings p l r) (pdCechBase p l r) :=
  NatIso.ofComponents (fun n => pdTermPointwiseCoefficientIso p k l r n.len)
    (fun {m n} θ => by
      obtain ⟨m⟩ := m
      obtain ⟨n⟩ := n
      exact pdTermPointwiseCoefficientIso_naturality p k l r θ)

/-- 各項の完備係数拡大後の交代余面複体の実際の比較同型。 -/
def pdCechPointwiseCoefficientCochainIso :
    (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{u} l)).obj
      (SerrePositivity.Cosimplicial.toModules k (pdCechRings p k r) (pdCechBase p k r) ⋙
        pCompletedScalarExtensionFunctor p (algebraMap k l)) ≅
    (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{u} l)).obj
      (SerrePositivity.Cosimplicial.toModules l (pdCechRings p l r) (pdCechBase p l r)) :=
  (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{u} l)).mapIso
    (pdCechPointwiseCoefficientIso p k l r)

end SerrePositivity.BhattScholze.Prismatic
