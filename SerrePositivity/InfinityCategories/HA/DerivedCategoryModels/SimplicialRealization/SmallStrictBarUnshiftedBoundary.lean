module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalValues
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardRowDifferential
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardZeroLeg
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalValues
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardRowCochain
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardZeroLeg
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.ZeroRowInclusion
import all SerrePositivity.HomologicalAlgebra.SimplicialReplacement

/-!
# シフト前の bar 列の同じ単体境界

## 概要
比較射の列の微分を、元の単体的置換の境界と同じ行の包含の合成へ戻す。

## 方針
標準列の全 cochain 境界式を、射列の同じ余積因子へ制限する。

## 規約
零次では既存の標準脚そのものと一致し、正次数では全ての面を保つ。

## 使われ方
HA 1.2.4。比較射の theta に対する閉性と指定脚の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open HomologicalComplex CochainComplex HomComplex SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

local instance smallStrictBarUnshiftedBoundary_hasCoproducts : HasCoproducts.{0} (Complex A) := fun _ =>
  HomologicalComplex.instHasColimitsOfShape

/-- 零次の標準 cochain は、既存の同じ標準脚の cochain。 -/
theorem standardRowCochain_zero (X : SimplicialObject (Complex A)) :
    standardRowCochain A X 0 = Cochain.ofHom (standardZeroLeg A X) := by
  apply Cochain.ext
  intro p q hpq
  have hq : q = p := by omega
  cases hq
  rw [standardRowCochain_v]
  rfl

/-- 零次の同じシフト前の bar 列は閉じている。 -/
theorem smallStrictBarUnshiftedColumn_zero_closed (F : J ⥤ ModuleCategory A PUnit.{1})
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋0⦌) :
    δ 0 1 (smallStrictBarUnshiftedColumn A F ⟨0, s⟩) = 0 := by
  dsimp only [smallStrictBarUnshiftedColumn]
  rw [standardRowCochain_zero, ← Cochain.ofHom_comp]
  exact δ_ofHom _

/-- 正次数の同じ列の微分は、元の置換の同じ単体境界の後の標準列。 -/
theorem smallStrictBarUnshiftedColumn_boundary (F : J ⥤ ModuleCategory A PUnit.{1}) (n : ℕ)
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n + 1⦌) :
    δ (-((n + 1 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ) + 1)
        (smallStrictBarUnshiftedColumn A F ⟨n + 1, s⟩) =
      (Cochain.ofHom
        (Sigma.ι (replacementTerms (smallStrictBarCoefficientDiagram A F) (op ⦋n + 1⦌)) s.down ≫
          (AlternatingFaceMapComplex.obj
            (simplicialReplacement (smallStrictBarCoefficientDiagram A F))).d (n + 1) n)).comp
        (standardRowCochain A (simplicialReplacement (smallStrictBarCoefficientDiagram A F)) n)
        (by omega) := by
  dsimp only [smallStrictBarUnshiftedColumn]
  rw [δ_ofHom_comp, standardRowCochain_δ]
  rw [← Cochain.comp_assoc _ _ _ (zero_add 0)
    (show (0 : ℤ) + -(n : ℤ) = -((n + 1 : ℕ) : ℤ) + 1 by omega)
    (show (0 : ℤ) + 0 + -(n : ℤ) = -((n + 1 : ℕ) : ℤ) + 1 by omega),
    ← Cochain.ofHom_comp]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
