module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Poincare.PDCompletedColumnContraction
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumnComparison
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Poincare.PDCompletedColumnContraction
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumnPoincare
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumnComparison
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCollapse

/-!
# 完備分冪 de Rham 総複体の第 0 列への射影

## 概要
p 完備な分冪 de Rham の各列を第 0 列に収縮し、総複体の列射影の擬同型を得る。

## 方針
有限個の差座標の評価を合成し、全座標の評価を第 0 頂点での余単体写像と照合する。
係数上の照合には未完備の分冪単項式の計算を使う。

## 規約
p の像が零であることは仮定しない。

## 使われ方
BS 著者版 Theorem 5.2 の複体の比較と Theorem 6.4 の厳密な zigzag。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DeRham SerrePositivity.DerivedCompletion
open scoped Simplicial TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ) (n : SimplexCategory)

local notation "S" => (Fin r × Fin n.len)
local notation "K" => pdDeRhamColumn p k r n
local notation "θ" => SimplexCategory.const n n 0

private def completedAllEvaluation (L : List S) : K ⟶ K :=
  L.foldr (fun s f => f ≫ pdCompletedCoordinateEvaluation p k r n s) (𝟙 K)

private theorem completedEvaluation_f (s : S) (j : ℕ) :
    (pdCompletedCoordinateEvaluation p k r n s).f j =
      ModuleCat.ofHom (TensorProduct.map (pdCompletedConstantTerm p k r n.len s)
        (exteriorPower.map j (copyEval k r n s))) := by
  cases j with
  | zero =>
    rw [pdCompletedCoordinateEvaluation_zero, copyEval, exteriorPower_map_coordinateProjection_zero]
  | succ j => exact pdCompletedCoordinateEvaluation_succ p k r n s j

private theorem completedAllEvaluation_f (L : List S) (j : ℕ) :
    (completedAllEvaluation p k r n L).f j =
      ModuleCat.ofHom (TensorProduct.map
        (principalCompletionLinearMap k p (A := pdRaw k r n.len) (B := pdRaw k r n.len)
          (allCoefficientsEval k r n L))
        (exteriorPower.map j (allCopyEval k r n L))) := by
  induction L with
  | nil =>
    simp [completedAllEvaluation, allCoefficientsEval, allCopyEval, completionLinearMap_id,
      TensorProduct.map_id]
    rfl
  | cons s L ih =>
    change (completedAllEvaluation p k r n L ≫ pdCompletedCoordinateEvaluation p k r n s).f j = _
    rw [HomologicalComplex.comp_f, ih, completedEvaluation_f]
    apply ModuleCat.hom_ext
    change (TensorProduct.map
      (principalCompletionLinearMap k p (A := pdRaw k r n.len) (B := pdRaw k r n.len)
        (pdRawConstantTerm k r n.len s))
      (exteriorPower.map j (copyEval k r n s))).comp
      (TensorProduct.map
        (principalCompletionLinearMap k p (A := pdRaw k r n.len) (B := pdRaw k r n.len)
          (allCoefficientsEval k r n L))
        (exteriorPower.map j (allCopyEval k r n L))) = _
    rw [← TensorProduct.map_comp, ← exteriorPower.map_comp, ← principalCompletionLinearMap_comp]
    rfl

private def completedAllEvaluationHomotopy (L : List S) :
    Homotopy (completedAllEvaluation p k r n L) (𝟙 K) :=
  match L with
  | [] => Homotopy.refl _
  | s :: L => ((completedAllEvaluationHomotopy L).comp
      (pdCompletedCoordinateEvaluationHomotopy p k r n s)).trans
        (Homotopy.ofEq (Category.id_comp _))

private theorem completionRawMap {m l : SimplexCategory} (f : m ⟶ l) :
    principalCompletionLinearMap k p (A := pdRaw k r m.len) (B := pdRaw k r l.len)
      (pdRawMap k r f).toLinearMap = pdTermMap p k r f := by
  apply principalCompletionLinearMap_ext k p (completedRing_isModuleComplete k p)
  intro x
  rw [principalCompletionLinearMap_unit]
  exact (pdTermMap_unit p k r f x).symm

private theorem completedAllEvaluation_const (L : List S) (hL : ∀ s, s ∈ L) :
    completedAllEvaluation p k r n L = pdDeRhamColumnMap p k r θ := by
  ext j : 1
  rw [completedAllEvaluation_f, allCoefficientsEval_const k r n L hL,
    allCopyEval_const k r n L hL, completionRawMap]
  rfl

/-- 各列で差座標を消す写像は、完備係数上でホモトピー同値。 -/
def pdDeRhamCompletedColumnCollapseHomotopyEquiv :
    HomotopyEquiv (pdDeRhamColumn p k r n) (pdDeRhamColumn p k r ⦋0⦌) where
  hom := pdDeRhamColumnCollapse p k r n
  inv := pdDeRhamColumnMap p k r (SimplexCategory.const ⦋0⦌ n 0)
  homotopyInvHomId := Homotopy.ofEq (pdDeRhamColumnCollapse_split p k r n)
  homotopyHomInvId := by
    classical
    let L := (Finset.univ : Finset S).toList
    have hL (s : S) : s ∈ L := by simp [L]
    have hθ : pdDeRhamColumnCollapse p k r n ≫
        pdDeRhamColumnMap p k r (SimplexCategory.const ⦋0⦌ n 0) =
          pdDeRhamColumnMap p k r θ := by
      rw [pdDeRhamColumnCollapse, pdDeRhamColumnMap_comp, collapseSimplex,
        ← SimplexCategory.const_fac_thru_zero]
    rw [hθ, ← completedAllEvaluation_const p k r n L hL]
    exact completedAllEvaluationHomotopy p k r n L

/-- 完備列から第 0 列への座標評価は擬同型。 -/
theorem pdDeRhamCompletedColumnCollapse_quasiIso : QuasiIso (pdDeRhamColumnCollapse p k r n) := by
  constructor
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact (pdDeRhamCompletedColumnCollapseHomotopyEquiv p k r n).toHomologyIso i |>.isIso_hom

/-- 完備係数の双複体で差座標を消す写像は、総複体で擬同型。 -/
theorem pdDeRhamCompletedCollapse_total_quasiIso :
    QuasiIso (HomologicalComplex₂.total.map (pdDeRhamCollapse p k r) (ComplexShape.up ℕ)) := by
  apply SerrePositivity.HomologicalAlgebra.bicomplexTotal_quasiIso_of_columns
  · intro a
    exact pdDeRhamCompletedColumnCollapse_quasiIso p k r ⦋a⦌
  · intro a b x
    let f := pdDeRhamColumnMap p k r (SimplexCategory.const ⦋0⦌ ⦋a⦌ 0)
    refine ⟨f.f b x, ?_⟩
    exact ConcreteCategory.congr_hom
      (congrArg (fun g => g.f b) (pdDeRhamColumnCollapse_split p k r ⦋a⦌)) x

/-- 完備分冪 de Rham 総複体から第 0 列への射影は擬同型。 -/
theorem pdDeRhamCompletedColumnZeroProjection_quasiIso :
    QuasiIso (pdDeRhamColumnZeroProjection p k r) := by
  rw [← pdDeRhamCollapse_projection p k r]
  let := pdDeRhamCompletedCollapse_total_quasiIso p k r
  let := constantColumnProjection_quasiIso p k r
  infer_instance

end SerrePositivity.BhattScholze.Prismatic
