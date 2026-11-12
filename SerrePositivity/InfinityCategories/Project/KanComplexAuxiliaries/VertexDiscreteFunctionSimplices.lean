module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.VertexDiscrete
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation

/-! # 離散頂点上の関手単体の座標表示
概要：全頂点の離散部分上の関手単体を、頂点ごとの単体の族と厳密に対応させる。
方針：内部 Hom の各単体を定値な離散変数で評価し、自然性で全次数へ戻す。
規約：添字の有限性や標的の Kan 性は不要。
使われ方：各対象での構造射の補正を、一つの固定端点の変換へ束ねる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalClosed SSet
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

/-- 離散頂点ごとの単体を、離散頂点上の内部 Hom の一つの単体にする。 -/
def vertexDiscreteFunctionSimplex {A X : SSet.{u}} {n : ℕ} (s : A _⦋0⦌ → X _⦋n⦌) :
    ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete A)).obj X) _⦋n⦌ where
  app d α := ↾fun a => X.map α (s a)
  naturality {d e} β α := by
    apply ConcreteCategory.hom_ext
    intro a
    exact X.map_comp_apply α β (s a)

/-- 離散変数を固定した内部 Hom の評価。 -/
def vertexDiscreteEvaluate {A X : SSet.{u}} (a : A _⦋0⦌) :
    (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete A)).obj X ⟶ X where
  app d := ↾fun s => s.app d (𝟙 d) a
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro s
    have hn := ConcreteCategory.congr_hom (s.naturality α (𝟙 d)) a
    change s.app e ((𝟙 d) ≫ α) a = X.map α (s.app d (𝟙 d) a) at hn
    change s.app e (α ≫ (𝟙 e)) a = X.map α (s.app d (𝟙 d) a)
    simpa only [Category.id_comp, Category.comp_id] using hn

/-- 座標から作った単体の評価は元の座標。 -/
lemma vertexDiscreteFunctionSimplex_evaluate {A X : SSet.{u}} {n : ℕ}
    (s : A _⦋0⦌ → X _⦋n⦌) (a : A _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a).app (Opposite.op ⦋n⦌) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex s) = s a :=
  X.map_id_apply (Opposite.op ⦋n⦌) (s a)

/-- 任意の内部 Hom 単体は、全ての離散頂点での評価から厳密に復元できる。 -/
lemma vertexDiscreteFunctionSimplex_reconstruct {A X : SSet.{u}} {n : ℕ}
    (s : ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete A)).obj X) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex (fun a => (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a).app (Opposite.op ⦋n⦌) s) = s := by
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro a
  have hn := ConcreteCategory.congr_hom (s.naturality α (𝟙 (Opposite.op ⦋n⦌))) a
  change s.app d ((𝟙 (Opposite.op ⦋n⦌)) ≫ α) a =
    X.map α (s.app (Opposite.op ⦋n⦌) (𝟙 _) a) at hn
  change X.map α (s.app (Opposite.op ⦋n⦌) (𝟙 _) a) = s.app d α a
  simpa only [Category.id_comp] using hn.symm

/-- 座標表示は全ての面・退化を保持する。 -/
lemma vertexDiscreteFunctionSimplex_map {A X : SSet.{u}} {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (s : A _⦋0⦌ → X _⦋n⦌) :
    ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete A)).obj X).map α.op (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex s) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex (fun a => X.map α.op (s a)) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro d β
  apply ConcreteCategory.hom_ext
  intro a
  exact X.map_comp_apply α.op β (s a)

/-- 離散図式の頂点表示の評価は元の図式の頂点の像。 -/
lemma vertexDiscreteEvaluate_functorVertex {A X : SSet.{u}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete A ⟶ X)
    (a : A _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) = F.app (Opposite.op ⦋0⦌) a := rfl

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.vertexDiscreteEvaluate := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.vertexDiscreteEvaluate_functorVertex := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate_functorVertex

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.vertexDiscreteFunctionSimplex := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.vertexDiscreteFunctionSimplex_evaluate := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex_evaluate

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.vertexDiscreteFunctionSimplex_map := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex_map

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.vertexDiscreteFunctionSimplex_reconstruct := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex_reconstruct

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.vertexDiscreteEvaluate._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.vertexDiscreteFunctionSimplex._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex._proof_1
