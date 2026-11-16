module
public import SerrePositivity.EInfinity.HomotopyWeight.Generators

/-!
概要：同じ単体集合図式圏の自由ホーン生成族を用意する。
方針：既存の自由評価随伴でホーンの小対象性と点ごとの右類を移す。
規約：IS-W2 R03a.1の証明分割。SSetモデル構造を仮定しない。
使われ方：同じ重み比較の射影anodyne・点ごとのfibration分解。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits
variable (K : Type u) [SmallCategory K]

/-- 元の全頂点で自由なホーンを合わせた生成族。 -/
abbrev horns : MorphismProperty (K ⥤ SSet.{u}) :=
  ModelGeneration.EvaluationFamily.generators (free K) SSet.modelCategoryQuillen.J

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

/-- 同じ自由ホーン生成族は、元の図式圏で小対象論法を許す。 -/
instance horns_smallObjectArgument : (horns K).HasSmallObjectArgument.{u} := by
  have hornFamilySmall : SSet.modelCategoryQuillen.J.{u}.IsSmall.{u} :=
    ModelGeneration.EvaluationFamily.isSmall_of_smallObjectArgument SSet.modelCategoryQuillen.J
  exact ModelGeneration.EvaluationFamily.generators_smallObjectArgument
    (free K) (evaluation K) (adjunction K) SSet.modelCategoryQuillen.J Cardinal.aleph0
    SimplicialModel.hornGenerator_domain_presentable

/-- 自由ホーンの右類は、元の図式の各値のホーンの右類。 -/
theorem horns_rlp : (horns K).rlp =
    ModelGeneration.EvaluationFamily.detected (evaluation K) SSet.modelCategoryQuillen.J.rlp :=
  ModelGeneration.EvaluationFamily.generators_rlp
    (free K) (evaluation K) (adjunction K) SSet.modelCategoryQuillen.J

end SerrePositivity.EInfinity.HomotopyWeight
