module

public import SerrePositivity.HomotopicalAlgebra.Complexes.ProjectiveModel
public import SerrePositivity.HomotopicalAlgebra.Transfer.EvaluationSmallness
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

/-!
# 複体図式の自由生成射族の具体的な小対象性

概要：Hovey §2.1・§2.3 の複体図式の射影モデルを具体的に構成する。
方針：評価随伴と実際の複体の生成族を使う。
規約：任意の小圏・可換環、局所表示可能性の追加仮定なし。
使われ方：底の定値図式からの局所化 Hom と一般右導来極限。
-/

@[expose] public section

noncomputable section

universe u v

namespace SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram

open CategoryTheory Limits HomotopicalAlgebra
open scoped ZeroObject
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

local instance : HasColimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩
/-- 概要：自由複体図式を指定頂点に追加する（Hovey §2.1・§2.3）。
方針：評価の左随伴を使う。
規約：各対象で元の複体の余積を取る。
使われ方：図式モデルの生成射。 -/
abbrev free (k : K) : Complex A ⥤ K ⥤ Complex A := evaluationLeftAdjoint (Complex A) k
/-- 概要：複体図式の指定頂点での評価（Hovey §2.1・§2.3）。
方針：元の関手の値と射を取る。
規約：添字圏は任意の小圏。
使われ方：図式モデルの右類の判定。 -/
abbrev evaluation (k : K) : (K ⥤ Complex A) ⥤ Complex A :=
  (CategoryTheory.evaluation K (Complex A)).obj k
/-- 概要：自由複体図式と評価の随伴（Hovey §2.1・§2.3）。
方針：余積による通常の評価随伴を使う。
規約：追加のモデル構造は不要。
使われ方：生成射の小対象性の移送。 -/
abbrev adjunction (k : K) : free A K k ⊣ evaluation A K k := evaluationAdjunctionRight _ k
/-- 概要：自由複体図式の生成射族（Hovey §2.1・§2.3）。
方針：元の射族の自由像を全頂点で合併する。
規約：元の射の厳密な関手像を使う。
使われ方：図式モデルの二つの小対象分解。 -/
abbrev generators (P : MorphismProperty (Complex A)) :=
  ModelGeneration.EvaluationFamily.generators (free A K) P
attribute [local instance] Cardinal.fact_isRegular_aleph0
/-- 概要：複体図式の自由生成族の小対象性（Hovey §2.1・§2.3）。
方針：元の始域の有限表示性を評価随伴で移す。
規約：局所表示可能性を入力仮定にしない。
使われ方：sphere と零複体による生成族。 -/
lemma freeFamily_smallObjectArgument {ι : Type v} [Small.{u} ι] {S T : ι → Complex A}
    (f : ∀ i, S i ⟶ T i) [∀ i, IsFinitelyPresentable.{u} (S i)] :
    (generators A K (MorphismProperty.ofHoms f)).HasSmallObjectArgument.{u} := by
  let κ : Cardinal.{u} := Cardinal.aleph0
  let : Fact κ.IsRegular := Cardinal.fact_isRegular_aleph0
  let : Nonempty κ.ord.ToType := Cardinal.nonempty_ord_toType (Fact.out : κ.IsRegular).ne_zero
  let : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot _
  have : (MorphismProperty.ofHoms f).IsSmall.{u} := inferInstance
  exact ModelGeneration.EvaluationFamily.generators_smallObjectArgument
    (free A K) (evaluation A K) (adjunction A K) (MorphismProperty.ofHoms f) κ (by
      intro X Y g hg
      cases hg with
      | mk i => exact inferInstance)
/-- 概要：図式の生成 cofibration の小対象性（Hovey §2.1・§2.3）。
方針：sphere の有限表示性を使う。
規約：任意の可換環と小圏。
使われ方：cofibration・trivial fibration 分解。 -/
instance generatingCofibrations_smallObjectArgument :
    (generators A K (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A)).HasSmallObjectArgument.{u} :=
  freeFamily_smallObjectArgument A K (complexSphereToDisk A)
/-- 概要：図式の生成 trivial cofibration の小対象性（Hovey §2.1・§2.3）。
方針：零複体の有限表示性を使う。
規約：元の図式の cofibrancy は不要。
使われ方：trivial cofibration・fibration 分解。 -/
instance generatingTrivialCofibrations_smallObjectArgument :
    (generators A K
      (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A)).HasSmallObjectArgument.{u} :=
  freeFamily_smallObjectArgument A K
    (fun n : ℤ => (0 : (HomologicalComplex.zero : Complex A) ⟶ complexDisk A n))

end SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram
