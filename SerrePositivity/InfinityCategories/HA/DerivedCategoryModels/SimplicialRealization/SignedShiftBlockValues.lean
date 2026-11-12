module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ShiftBlockValues
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ShiftBlockValues

/-!
# 外側の符号を含む同じ一次 shift ブロックの評価

## 概要
bar の一次列の外側の符号と、元の二つの shift 単位の符号を相殺する。

## 方針
既存のブロックの評価公式と連続する shift 単位の符号の積の公式を使う。

## 規約
元の次数同型・係数・shift ブロックを変更しない。

## 使われ方
HA 1.2.4。theta の一次列と単体境界の同じ成分の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
variable (A : Type u) [CommRing A]

/-- 外側の (-1)^(n+1) を含めると、二つの shift 単位の定数符号は完全に相殺する。 -/
theorem signedShiftBlock_v (n : ℕ) (M N : RightModule A PUnit.{1})
    (f : (moduleHom A PUnit.{1} M N).X 0) (p : ℤ) :
    (((moduleHomπ A PUnit.{1} (shiftModule ((n + 1 : ℕ) : ℤ) M) (shiftModule (n : ℤ) N)
        PUnit.unit).f 1
      (((n + 1 : ℕ) : ℤ).negOnePow • moduleHomShiftBlock A PUnit.{1}
        ((n + 1 : ℕ) : ℤ) (n : ℤ) f (by omega))).v p (p + 1) rfl) =
      ((M.obj (op PUnit.unit)).shiftFunctorObjXIso ((n + 1 : ℕ) : ℤ) p
        (p + ((n + 1 : ℕ) : ℤ)) rfl).hom ≫
      (((moduleHomπ A PUnit.{1} M N PUnit.unit).f 0 f).v
        (p + ((n + 1 : ℕ) : ℤ)) (p + ((n + 1 : ℕ) : ℤ)) (by omega)) ≫
      ((N.obj (op PUnit.unit)).shiftFunctorObjXIso (n : ℤ) (p + 1)
        (p + ((n + 1 : ℕ) : ℤ)) (by omega)).inv := by
  have he := map_zsmul
    (((moduleHomπ A PUnit.{1} (shiftModule ((n + 1 : ℕ) : ℤ) M) (shiftModule (n : ℤ) N)
      PUnit.unit).f 1).hom)
    ((((n + 1 : ℕ) : ℤ).negOnePow : ℤ))
    (moduleHomShiftBlock A PUnit.{1} ((n + 1 : ℕ) : ℤ) (n : ℤ) f (k := 1) (by omega))
  let b := moduleHomShiftBlock A PUnit.{1} ((n + 1 : ℕ) : ℤ) (n : ℤ) f (k := 1) (by omega)
  let π := (moduleHomπ A PUnit.{1} (shiftModule ((n + 1 : ℕ) : ℤ) M)
    (shiftModule (n : ℤ) N) PUnit.unit).f 1
  have hu : π (((n + 1 : ℕ) : ℤ).negOnePow • b) =
      ((n + 1 : ℕ) : ℤ).negOnePow • π b := he
  have h₁ := congrArg (fun z : Cochain
    ((shiftModule ((n + 1 : ℕ) : ℤ) M).obj (op PUnit.unit))
    ((shiftModule (n : ℤ) N).obj (op PUnit.unit)) 1 => z.v p (p + 1) rfl) hu
  have hb := dgBarShiftBlock_v A PUnit.{1} ((n + 1 : ℕ) : ℤ) (n : ℤ) f
    (show ((n + 1 : ℕ) : ℤ) + 0 - (n : ℤ) = 1 by omega) PUnit.unit p (p + 1) rfl
  have hs : dgBarShiftUnitSign ((n + 1 : ℕ) : ℤ) * dgBarShiftUnitSign (n : ℤ) =
      ((n + 1 : ℕ) : ℤ).negOnePow := by
    simpa only [Nat.cast_add, Nat.cast_one] using dgBarShiftUnitSign_succ_mul (n : ℤ)
  exact h₁.trans
    ((Cochain.units_smul_v ((n + 1 : ℕ) : ℤ).negOnePow (π b) p (p + 1) rfl).trans
      ((congrArg (fun z => ((n + 1 : ℕ) : ℤ).negOnePow • z) hb).trans (by
        rw [smul_smul, hs, Int.units_mul_self, one_smul])))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
