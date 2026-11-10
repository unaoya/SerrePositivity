module

public import SerrePositivity.CommutativeAlgebra.DeRham.Polynomial

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Algebra.Algebra.RestrictScalars

/-!
# 自由加群の外冪の係数変換

## 概要
有限台の自由加群とその外冪を係数環の準同型に沿って写す。

## 方針
一次の写像を外積代数の普遍性で延長し、斉次成分を保つことを外積単項式で示す。

## 規約
終域の加群を元の係数環に制限して線形写像とする。

## 使われ方
整係数 pd de Rham 模型から mod p への還元。
-/

public noncomputable section

universe u

namespace SerrePositivity.DeRham

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (I : Type)

local notation "M" => I →₀ A
local notation "N" => I →₀ B

/-- 自由加群の係数を代数写像で変換する。 -/
def freeCoefficientMap : M →ₗ[A] N :=
  Finsupp.mapRange.linearMap (Algebra.linearMap A B)

local notation "E" => RestrictScalars A B (ExteriorAlgebra B (N))

set_option backward.isDefEq.respectTransparency false in
private def exteriorGenerator : N →ₗ[A] E where
  toFun := ExteriorAlgebra.ι B
  map_add' := (ExteriorAlgebra.ι B).map_add
  map_smul' a x := by
    have hx : a • x = (algebraMap A B a) • x := by
      ext i
      simp only [Finsupp.smul_apply, Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]
    let e := RestrictScalars.addEquiv A B (ExteriorAlgebra B N)
    apply e.injective
    rw [RingHom.id_apply, RestrictScalars.addEquiv_map_smul]
    change ExteriorAlgebra.ι B (a • x) = (algebraMap A B a) • ExteriorAlgebra.ι B x
    rw [hx, map_smul]

private def exteriorAlgebraCoeff :
    ExteriorAlgebra A (M) →ₐ[A] E :=
  ExteriorAlgebra.lift A
    ⟨(exteriorGenerator A B I).comp (freeCoefficientMap A B I),
      fun m => ExteriorAlgebra.ι_sq_zero (freeCoefficientMap A B I m)⟩

private theorem exteriorAlgebraCoeff_ι (m : M) :
    exteriorAlgebraCoeff A B I (ExteriorAlgebra.ι A m) =
      ExteriorAlgebra.ι B (freeCoefficientMap A B I m) :=
  ExteriorAlgebra.lift_ι_apply A ((exteriorGenerator A B I).comp (freeCoefficientMap A B I))
    (fun x => ExteriorAlgebra.ι_sq_zero (freeCoefficientMap A B I x)) m

private theorem exteriorAlgebraCoeff_ιMulti {j : ℕ} (m : Fin j → M) :
    exteriorAlgebraCoeff A B I (ExteriorAlgebra.ιMulti A j m) =
      ExteriorAlgebra.ιMulti B j (freeCoefficientMap A B I ∘ m) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod]
  rw [List.map_ofFn]
  exact congrArg List.prod (congrArg List.ofFn (funext
    fun i => exteriorAlgebraCoeff_ι A B I (m i)))

private theorem exteriorAlgebraCoeff_mem (j : ℕ) {z : ExteriorAlgebra A (M)}
    (hz : z ∈ (⋀[A]^j (M))) :
    exteriorAlgebraCoeff A B I z ∈ (⋀[B]^j (N)) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m,rfl⟩ := hx
    rw [exteriorAlgebraCoeff_ιMulti]
    exact ExteriorAlgebra.ιMulti_range B j (Set.mem_range_self _)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ (algebraMap A B a) hx

/-- 自由加群の斉次外冪の係数変換。 -/
def exteriorPowerCoefficientMap (j : ℕ) :
    (⋀[A]^j (M)) →+ (⋀[B]^j (N)) where
  toFun z := ⟨exteriorAlgebraCoeff A B I z.1, exteriorAlgebraCoeff_mem A B I j z.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- 外冪の係数変換は一次の外積単項式を係数変換した外積に送る。 -/
theorem exteriorPowerCoefficientMap_ιMulti {j : ℕ} (m : Fin j → M) :
    exteriorPowerCoefficientMap A B I j (exteriorPower.ιMulti A j m) =
      exteriorPower.ιMulti B j (freeCoefficientMap A B I ∘ m) :=
  Subtype.ext (exteriorAlgebraCoeff_ιMulti A B I m)

/-- 自由加群の係数変換は単位係数の座標を保つ。 -/
theorem freeCoefficientMap_single (i : I) :
    freeCoefficientMap A B I (Finsupp.single i 1) = Finsupp.single i 1 := by
  classical
  ext j
  simp only [freeCoefficientMap, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
    Algebra.linearMap_apply, Finsupp.single_apply, apply_ite, map_one, map_zero]
  split <;> simp_all

/-- 自由加群の係数変換は座標の写像と可換。 -/
theorem freeCoefficientMap_mapDomain {J : Type} (f : I → J) (m : M) :
    freeCoefficientMap A B J (Finsupp.mapDomain f m) =
      Finsupp.mapDomain f (freeCoefficientMap A B I m) :=
  (Finsupp.mapDomain_mapRange f m (algebraMap A B) (map_zero _) (map_add _)).symm

/-- 外冪の係数変換を半線形写像として使う。 -/
def exteriorPowerCoefficients (j : ℕ) :
    (⋀[A]^j (M)) →ₛₗ[algebraMap A B] (⋀[B]^j (N)) where
  toAddHom := exteriorPowerCoefficientMap A B I j
  map_smul' a z := Subtype.ext ((exteriorAlgebraCoeff A B I).toLinearMap.map_smul a z.1)

/-- 係数変換は外積と可換。 -/
theorem exteriorPowerCoefficients_wedge {i j : ℕ}
    (x : ⋀[A]^i (M)) (y : ⋀[A]^j (M)) :
    exteriorPowerCoefficients A B I (i+j) (exteriorWedge A M i j x y) =
      exteriorWedge B N i j (exteriorPowerCoefficients A B I i x)
        (exteriorPowerCoefficients A B I j y) :=
  Subtype.ext (map_mul (exteriorAlgebraCoeff A B I) x.1 y.1)

/-- 一次形式を左から外積する写像は係数変換と可換。 -/
theorem exteriorPowerCoefficients_wedgeOne (j : ℕ) (x : ⋀[A]^1 (M)) (y : ⋀[A]^j (M)) :
    exteriorPowerCoefficients A B I (j+1) (wedgeOne A M j x y) =
      wedgeOne B N j (exteriorPowerCoefficients A B I 1 x) (exteriorPowerCoefficients A B I j y) := by
  apply Subtype.ext
  change exteriorAlgebraCoeff A B I (wedgeOne A M j x y).1 =
    (wedgeOne B N j (exteriorPowerCoefficients A B I 1 x)
      (exteriorPowerCoefficients A B I j y)).1
  rw [wedgeOne_coe, wedgeOne_coe]
  exact map_mul (exteriorAlgebraCoeff A B I) x.1 y.1

/-- 係数変換は一次形式の同一視を保つ。 -/
theorem exteriorPowerCoefficients_one (x : M) :
    exteriorPowerCoefficients A B I 1 ((exteriorPower.oneEquiv A M).symm x) =
      (exteriorPower.oneEquiv B N).symm (freeCoefficientMap A B I x) := by
  rw [exteriorPower.oneEquiv_symm_apply, exteriorPower.oneEquiv_symm_apply]
  exact exteriorPowerCoefficientMap_ιMulti A B I (fun _ => x)

/-- 座標の写像から誘導される外冪の写像は係数変換と可換。 -/
theorem exteriorPowerCoefficients_mapDomain {J : Type} (f : I → J) (j : ℕ)
    (x : ⋀[A]^j (M)) :
    exteriorPowerCoefficients A B J j (exteriorPower.map j (Finsupp.lmapDomain A A f) x) =
      exteriorPower.map j (Finsupp.lmapDomain B B f) (exteriorPowerCoefficients A B I j x) := by
  have hx : x ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A j : (Fin j → M) → _)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m,rfl⟩ := hz
    simp only [exteriorPower.map_apply_ιMulti]
    have h (I' : Type) (v : Fin j → I' →₀ A) :
        exteriorPowerCoefficients A B I' j (exteriorPower.ιMulti A j v) =
          exteriorPower.ιMulti B j (freeCoefficientMap A B I' ∘ v) :=
      exteriorPowerCoefficientMap_ιMulti A B I' v
    rw [h, h, exteriorPower.map_apply_ιMulti]
    congr 1
    funext i
    exact freeCoefficientMap_mapDomain A B I f (m i)
  | zero => simp only [map_zero]
  | add _ _ _ _ hx hy => simp only [map_add, hx, hy]
  | smul a z _ hz => simp only [map_smul, LinearMap.map_smulₛₗ, hz]

end SerrePositivity.DeRham
