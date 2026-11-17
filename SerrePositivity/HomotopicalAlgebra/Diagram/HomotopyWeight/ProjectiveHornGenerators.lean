module
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.Generators

/-!
概要：同じ単体集合図式圏の自由ホーン生成族を用意する。
方針：既存の自由評価随伴でホーンの小対象性と点ごとの右類を移す。
規約：IS-W2 R03a.1の証明分割。SSetモデル構造を仮定しない。
使われ方：同じ重み比較の射影anodyne・点ごとのfibration分解。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
open _root_.CategoryTheory _root_.CategoryTheory.Limits
variable (K : Type u) [SmallCategory K]

/-- 元の全頂点で自由なホーンを合わせた生成族。 -/
abbrev horns : MorphismProperty (K ⥤ SSet.{u}) :=
  _root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.free K) SSet.modelCategoryQuillen.J

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

/-- 同じ自由ホーン生成族は、元の図式圏で小対象論法を許す。 -/
instance horns_smallObjectArgument : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.horns K).HasSmallObjectArgument.{u} := by
  have hornFamilySmall : SSet.modelCategoryQuillen.J.{u}.IsSmall.{u} :=
    _root_.SerrePositivity.ModelGeneration.EvaluationFamily.isSmall_of_smallObjectArgument SSet.modelCategoryQuillen.J
  exact _root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators_smallObjectArgument
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.free K) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.evaluation K) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.adjunction K) SSet.modelCategoryQuillen.J Cardinal.aleph0
    _root_.SerrePositivity.SimplicialModel.hornGenerator_domain_presentable

/-- 自由ホーンの右類は、元の図式の各値のホーンの右類。 -/
theorem horns_rlp : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.horns K).rlp =
    _root_.SerrePositivity.ModelGeneration.EvaluationFamily.detected (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.evaluation K) SSet.modelCategoryQuillen.J.rlp :=
  _root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators_rlp
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.free K) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.evaluation K) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.adjunction K) SSet.modelCategoryQuillen.J

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
