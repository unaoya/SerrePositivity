module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRowFormsExt
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDCompletedSubstitutionNaturality
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRowFormsExt
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamSubstitutionDegreeZero
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamSubstitutionWedge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDCompletedSubstitutionNaturality
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCompletedSubstitution
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamSubstitutionForms
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 完備分冪 de Rham の代入と余単体構造

## 概要
各外次数で多項式代入と余面・余退化が厳密に可換である。

## 方針
両合成が微分を保つことから、係数の代入と余単体構造の可換性に帰着する。

## 規約
余単体の任意の射について一つの等式で述べる。

## 使われ方
BS 著者版 Theorem 6.4 の完備分冪 de Rham 双複体の多項式代入。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion SerrePositivity.KST.DerivedBlowup
open scoped TensorProduct Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [CommRing k] (p : ℕ) (r : ℕ)
variable {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)

private def cofaceRing : pdTerm p k r m →ₐ[k] pdTerm p k r n :=
  let f := ringCatMap p (rawTermMap k r θ)
  ⟨f.hom, fun c => by
    let jM := principalCompletionRingCatUnit p (CommRingCat.of (pdRaw k r m))
    let jN := principalCompletionRingCatUnit p (CommRingCat.of (pdRaw k r n))
    change f (jM (algebraMap k (pdRaw k r m) c)) = jN (algebraMap k (pdRaw k r n) c)
    exact (ConcreteCategory.congr_hom (ringCatMap_comp_unit p (rawTermMap k r θ)) _).trans
      (congrArg jN ((pdRawMap k r θ).commutes c))⟩

private def cofaceExterior :
    pdTerm p k r m ⊗[k] ExteriorAlgebra k (CopyModule k r ⦋m⦌) →ₐ[k]
      pdTerm p k r n ⊗[k] ExteriorAlgebra k (CopyModule k r ⦋n⦌) :=
  Algebra.TensorProduct.map (cofaceRing p r θ) (ExteriorAlgebra.map (copyModuleMap k r θ))

private theorem coface_inclusion (i : ℕ) (x : (pdRow p k r i).obj ⦋m⦌) :
    rowFormsInclusion (k := k) p r n i ((pdRow p k r i).map θ x) =
      cofaceExterior p r θ (rowFormsInclusion (k := k) p r m i x) := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb =>
    unfold rowFormsInclusion at ha hb ⊢
    simp only [map_add, ha, hb]
  | tmul a z =>
    change pdTerm p k r m at a
    change ⋀[k]^i (CopyModule k r ⦋m⦌) at z
    change exteriorBaseChangeDegreeInclusion i
      (TensorProduct.map (pdTermMap p k r θ) (exteriorPower.map i (copyModuleMap k r θ))
        (a ⊗ₜ[k] z)) = _
    rw [TensorProduct.map_tmul]
    change pdTermMap p k r θ a ⊗ₜ[k] (exteriorPower.map i (copyModuleMap k r θ) z).val =
      cofaceExterior p r θ (a ⊗ₜ[k] z.val)
    rw [exteriorPower.coe_map, cofaceExterior, Algebra.TensorProduct.map_tmul]
    rfl

private theorem coface_zero (a : pdTerm p k r m) :
    (pdRow p k r 0).map θ (a ⊗ₜ[k] (exteriorPower.zeroEquiv k (CopyModule k r ⦋m⦌)).symm 1) =
      cofaceRing p r θ a ⊗ₜ[k] (exteriorPower.zeroEquiv k (CopyModule k r ⦋n⦌)).symm 1 := by
  change TensorProduct.map (pdTermMap p k r θ) (exteriorPower.map 0 (copyModuleMap k r θ))
    (a ⊗ₜ[k] (exteriorPower.zeroEquiv k (CopyModule k r ⦋m⦌)).symm 1) = _
  rw [TensorProduct.map_tmul]
  congr 1
  apply Subtype.ext
  rw [exteriorPower.coe_map, exteriorZero_one, exteriorZero_one, map_one]

private theorem coface_d (j : ℕ) :
    (pdRow p k r j).map θ ≫ pdVerticalD p k r ⦋n⦌ j =
      pdVerticalD p k r ⦋m⦌ j ≫ (pdRow p k r (j + 1)).map θ :=
  (pdDeRhamDifferential p k r j).naturality θ

variable [Fact p.Prime]
variable {J : Ideal k} (γ : DividedPowers J)
variable (hk : IsAdicComplete (Ideal.span {(p : k)}) k)
variable (hr : Function.Injective (fun x : k => (p : k) * x))
variable {Q Q' : Poly k} (f : Q ⟶ Q')

local notation "e" => substituteRowForms p γ hk hr f
local notation "E" a => substituteExterior p γ hk hr f a

private theorem completed_naturality (x : pdTerm p k Q.n m) :
    substituteCompleted p γ hk hr f n (cofaceRing p Q.n θ x) =
      cofaceRing p Q'.n θ (substituteCompleted p γ hk hr f m x) := by
  let S := (completedSubstitutionFunctor p γ hk hr).map f
  have h := S.naturality θ
  have h' := congrArg (fun g => g.right) h
  exact ConcreteCategory.congr_hom h' x

private theorem coface_square_zero :
    (pdRow p k Q.n 0).map θ ≫ (e n 0) =
      (e m 0) ≫ (pdRow p k Q'.n 0).map θ := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a w
  change pdTerm p k Q.n m at a
  let M := CopyModule k Q.n ⦋m⦌
  obtain ⟨c, rfl⟩ := (exteriorPower.zeroEquiv k M).symm.surjective w
  have hc : (exteriorPower.zeroEquiv k M).symm c =
      c • (exteriorPower.zeroEquiv k M).symm 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [hc, ← TensorProduct.smul_tmul]
  change (e n 0) ((pdRow p k Q.n 0).map θ
      ((c • a) ⊗ₜ[k] (exteriorPower.zeroEquiv k M).symm 1)) =
    (pdRow p k Q'.n 0).map θ ((e m 0)
      ((c • a) ⊗ₜ[k] (exteriorPower.zeroEquiv k M).symm 1))
  rw [coface_zero]
  change substituteForms p γ hk hr f n 0
      (cofaceRing p Q.n θ (c • a) ⊗ₜ[k]
        (exteriorPower.zeroEquiv k (CopyModule k Q.n ⦋n⦌)).symm 1) =
    (pdRow p k Q'.n 0).map θ
      (substituteForms p γ hk hr f m 0
        ((c • a) ⊗ₜ[k] (exteriorPower.zeroEquiv k M).symm 1))
  rw [substituteForms_zero, substituteForms_zero, coface_zero, completed_naturality]

/-- 完備分冪形式の代入はすべての余面・余退化と可換。 -/
theorem substituteRowForms_natural (i : ℕ) :
    (pdRow p k Q.n i).map θ ≫ (e n i) =
      (e m i) ≫ (pdRow p k Q'.n i).map θ := by
  refine rowForms_ext (k := k) p Q Q'.n n m
    (fun j => (pdRow p k Q.n j).map θ ≫ (e n j))
    (fun j => (e m j) ≫ (pdRow p k Q'.n j).map θ)
    ((E n).comp (cofaceExterior p Q.n θ)) ((cofaceExterior p Q'.n θ).comp (E m))
    ?_ ?_ ?_ ?_ ?_ i
  · intro j x
    simp only [ConcreteCategory.comp_apply, AlgHom.comp_apply]
    change exteriorBaseChangeDegreeInclusion j
      (substituteForms p γ hk hr f n j ((pdRow p k Q.n j).map θ x)) = _
    rw [map_inclusion]
    exact congrArg (fun x => (E n) x) (coface_inclusion p Q.n θ j x)
  · intro j x
    simp only [ConcreteCategory.comp_apply, AlgHom.comp_apply]
    rw [coface_inclusion]
    exact congrArg (cofaceExterior p Q'.n θ) (map_inclusion p γ hk hr f m j x)
  · intro j
    simp only [Category.assoc, substituteRowForms_d]
    rw [← Category.assoc, coface_d p Q.n θ j, Category.assoc]
  · intro j
    rw [Category.assoc, coface_d p Q'.n θ j,
      ← Category.assoc, substituteRowForms_d, Category.assoc]
  · exact coface_square_zero p θ γ hk hr f

end SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution
