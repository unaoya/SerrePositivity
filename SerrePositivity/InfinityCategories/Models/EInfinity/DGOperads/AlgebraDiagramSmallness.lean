module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraSmallObject
public import SerrePositivity.HomotopicalAlgebra.Transfer.EvaluationSmallness
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

/-!
模型。文献の定義との比較は後で
# 小さい代数図式の自由生成射の小対象性

概要：BM 命題 4.1 の生成射を任意の小圏の各頂点で自由に追加する。
方針：自由代数の有限表示性と評価の余極限保存から小対象性を得る。
規約：図式の添字と基礎環は同じ宇宙、図式モデルの存在は仮定しない。
使われ方：E2a-4 の一般図式の導来比較のための射影図式モデル。
-/

@[expose] public section

noncomputable section

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraDiagram

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A] (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Type u) [SmallCategory K]

set_option synthInstance.maxHeartbeats 40000 in
/-- 概要：指定した頂点に自由な代数図式を追加する（BM §1）。
方針：評価の左随伴を使う。
規約：他の頂点には各射で添字付けた余積を置く。
使われ方：図式モデルの生成射の自由像。 -/
abbrev free (k : K) : P.Algebra ⥤ K ⥤ P.Algebra := evaluationLeftAdjoint P.Algebra k

/-- 概要：代数図式の指定した頂点を評価する（BM §1）。
方針：通常の関手圏の評価を使う。
規約：底の代数も作用も保持する。
使われ方：図式の右類の頂点ごとの判定。 -/
abbrev evaluation (k : K) : (K ⥤ P.Algebra) ⥤ P.Algebra :=
  (CategoryTheory.evaluation K P.Algebra).obj k

set_option synthInstance.maxHeartbeats 40000 in
/-- 概要：自由図式と評価の随伴（BM §1）。
方針：余積による評価随伴を使う。
規約：通常の関手圏そのものの随伴。
使われ方：生成射の持ち上げ性と有限表示性の移送。 -/
abbrev adjunction (k : K) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraDiagram.free P K k ⊣ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraDiagram.evaluation P K k :=
  evaluationAdjunctionRight P.Algebra k

/-- 概要：各頂点の自由図式で生成する射族（BM 命題 4.1）。
方針：自由像を全頂点について合併する。
規約：元の代数の生成射族を入力とする。
使われ方：図式モデルの二つの生成類。 -/
abbrev generators (Q : MorphismProperty P.Algebra) :=
  _root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraDiagram.free P K) Q

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- 概要：元の生成射の自由代数像から自由図式像への小対象性（BM 命題 4.1）。
方針：生成射の始域の有限表示性を二つの左随伴で移す。
規約：代数図式圏の局所有限表示性を入力に要求しない。
使われ方：I と J の両図式生成族に同じ小対象論法を適用する。 -/
lemma freeFamily_smallObjectArgument {ι : Type v} [Small.{u} ι] {S T : ι → Complex A}
    (f : ∀ i, S i ⟶ T i) [∀ i, IsFinitelyPresentable.{u} (S i)] :
    MorphismProperty.HasSmallObjectArgument.{u}
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraDiagram.generators P K ((MorphismProperty.ofHoms f).strictMap P.freeAlgebraFunctor)) := by
  let κ : Cardinal.{u} := Cardinal.aleph0
  let : Fact κ.IsRegular := Cardinal.fact_isRegular_aleph0
  let : Nonempty κ.ord.ToType := Cardinal.nonempty_ord_toType (Fact.out : κ.IsRegular).ne_zero
  let : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot _
  have : (MorphismProperty.ofHoms f).IsSmall.{u} := inferInstance
  have : ((MorphismProperty.ofHoms f).strictMap P.freeAlgebraFunctor).IsSmall.{u} :=
    _root_.SerrePositivity.ModelGeneration.EvaluationFamily.isSmall_strictMap _ _
  exact _root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators_smallObjectArgument
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraDiagram.free P K) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraDiagram.evaluation P K) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraDiagram.adjunction P K)
    ((MorphismProperty.ofHoms f).strictMap P.freeAlgebraFunctor) κ (by
      intro X Y g hg
      cases hg with
      | map hg =>
        cases hg with
        | mk i => exact inferInstance)

/-- 概要：図式の自由像の生成 cofibration は小対象論法を許す（BM 命題 4.1）。
方針：元の sphere の有限表示性に一般の射族の判定を適用する。
規約：任意の小圏と任意の可換基礎環。
使われ方：図式の cofibration・trivial fibration 分解。 -/
instance generatingCofibrations_smallObjectArgument :
    MorphismProperty.HasSmallObjectArgument.{u}
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraDiagram.generators P K ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).strictMap P.freeAlgebraFunctor)) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraDiagram.freeFamily_smallObjectArgument P K (complexSphereToDisk A)

/-- 概要：図式の自由像の生成 trivial cofibration は小対象論法を許す（BM 命題 4.1）。
方針：零複体の有限表示性に同じ一般の判定を適用する。
規約：代数図式の始域の cofibrancy を仮定しない。
使われ方：図式の trivial cofibration・fibration 分解。 -/
instance generatingTrivialCofibrations_smallObjectArgument :
    MorphismProperty.HasSmallObjectArgument.{u} (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraDiagram.generators P K
      ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A).strictMap P.freeAlgebraFunctor)) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraDiagram.freeFamily_smallObjectArgument P K
    (fun n : ℤ => (0 : (HomologicalComplex.zero : Complex A) ⟶ complexDisk A n))

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraDiagram
