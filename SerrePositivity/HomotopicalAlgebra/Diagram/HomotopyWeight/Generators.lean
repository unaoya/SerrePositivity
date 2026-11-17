module
public import SerrePositivity.HomotopicalAlgebra.Transfer.EvaluationSmallness

public import SerrePositivity.HomotopicalAlgebra.Simplicial.Generators
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

/-!
# Homotopy 極限の重みの射影境界生成族

概要：Hovey §5 の小図式の単体的重みに対し、各頂点の自由境界生成族を構成する。
方針：境界の有限表示性と自由・評価随伴から小対象性を得る。
規約：単体集合の完全なモデル構造を仮定しない。
使われ方：定値一点重みの射影 cofibrant 置換。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable (K : Type u) [SmallCategory K]

/-- 概要：指定した頂点に自由な単体集合の図式を追加する（Hovey §5）。
方針：通常の評価の左随伴を使う。
規約：図式の射で添字付けた余積を各頂点に置く。
使われ方：境界生成族の自由像。 -/
abbrev free (k : K) : SSet.{u} ⥤ K ⥤ SSet.{u} := evaluationLeftAdjoint SSet.{u} k

/-- 概要：重みの図式を指定した頂点で評価する（Hovey §5）。
方針：通常の関手圏の評価を使う。
規約：各単体と作用素を保持する。
使われ方：右持ち上げ性を頂点ごとに判定する。 -/
abbrev evaluation (k : K) : (K ⥤ SSet.{u}) ⥤ SSet.{u} :=
  (CategoryTheory.evaluation K SSet.{u}).obj k

/-- 概要：自由な重みと評価の実際の随伴（Hovey §5）。
方針：余積からの射と指定した頂点への射を同定する。
規約：元の通常の図式圏での随伴。
使われ方：境界の小対象性と持ち上げの移送。 -/
abbrev adjunction (k : K) : _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.free K k ⊣ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.evaluation K k :=
  evaluationAdjunctionRight SSet.{u} k

/-- 概要：すべての頂点の自由境界を合わせた生成族（Hovey §5）。
方針：実際の単体境界包含の自由像を合併する。
規約：arity やモデル構造を追加しない。
使われ方：定値一点への射の左・右持ち上げ分解。 -/
abbrev boundaries : MorphismProperty (K ⥤ SSet.{u}) :=
  _root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.free K) SSet.modelCategoryQuillen.I

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

/-- 概要：自由境界生成族は小対象論法を許す（Hovey §2.1・§5）。
方針：各境界の有限表示性を自由評価随伴で移し、正則基数 ℵ₀ を使う。
規約：図式モデルや単体集合モデルの存在は入力しない。
使われ方：重みの実際の射影 cofibrant 置換を選ぶ。 -/
instance boundaries_smallObjectArgument : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries K).HasSmallObjectArgument.{u} := by
  have : SSet.modelCategoryQuillen.I.{u}.IsSmall.{u} :=
    _root_.SerrePositivity.SimplicialModel.boundaryGenerators_isSmall
  exact _root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators_smallObjectArgument
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.free K) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.evaluation K) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.adjunction K) SSet.modelCategoryQuillen.I Cardinal.aleph0
    _root_.SerrePositivity.SimplicialModel.boundaryGenerator_domain_presentable

/-- 概要：自由境界の右類は各頂点の境界の右類（Hovey §2.1・§5）。
方針：自由評価随伴で持ち上げを移す。
規約：右類は実際の Mathlib の境界生成族の rlp。
使われ方：重みの各値から一点への自明 Kan fibration を得る。 -/
lemma boundaries_rlp : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries K).rlp =
    _root_.SerrePositivity.ModelGeneration.EvaluationFamily.detected (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.evaluation K) SSet.modelCategoryQuillen.I.rlp :=
  _root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators_rlp
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.free K) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.evaluation K) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.adjunction K) SSet.modelCategoryQuillen.I

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
