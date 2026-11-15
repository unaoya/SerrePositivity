module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardHomTopProjection
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedDifferential
public import Mathlib.AlgebraicTopology.DoldKan.Normalized

/-!
# 正規化標準 Hom の最上位評価の回収

概要：元の標準単体を指定 Moore 射影で正規化しても最上位評価は元の値となる。
方針：同じ正規化包含との可換式を射影の因子分解に代入する。
規約：正規化の選択と評価射は本体の定義を保持する。
使われ方：HA 1.2.4、Kerodon 2.5（Tag 00ND）の指定 AW 合成の成分照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory DifferentialGraded AlgebraicTopology
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories
open DifferentialGradedCategories
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：正規化最上位評価は包含の後の生の評価である。
方針：既存の具体的正規化部分加群との可換式を使う。
規約：正次数の同じ射。使われ方：HA 1.2.4 の DK 正規化の評価。 -/
theorem standardMooreTopMap_inclusion (x y : D) (n : ℕ) :
    standardMooreTopMap (R := R) x y n =
      (inclusionOfMooreComplexMap (standardModule (R := R) x y)).f (n + 1) ≫
        ModuleCat.ofHom (standardTopEval (R := R) x y (n + 1)) := by
  rw [inclusionOfMooreComplexMap_f, ← standardMooreTermIso_hom_subtype]
  dsimp only [standardMooreTopMap]
  rw [Category.assoc]
  rfl

/-- 概要：Moore 射影による正規化から元の最上位成分を回収する。
方針：包含との因子分解を既存の射影消去式に接続する。
規約：全正次数、元の指定射影。使われ方：HA 1.2.4 の実豊穣合成との照合。 -/
theorem standardMooreTopMap_projection (x y : D) (n : ℕ) :
    (DoldKan.PInftyToNormalizedMooreComplex (standardModule (R := R) x y)).f (n + 1) ≫
      standardMooreTopMap (R := R) x y n =
    ModuleCat.ofHom (standardTopEval (R := R) x y (n + 1)) := by
  rw [standardMooreTopMap_inclusion, ← Category.assoc,
    ← HomologicalComplex.comp_f,
    DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap,
    standardTopEval_PInfty]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
