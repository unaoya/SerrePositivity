module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeColimitFunctorIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.ComparisonCartesian

/-!
概要：指定変換の相対左 Kan 条件と局所輸送の選択不変性。
方針：標準 U 余極限を比較余錐に課し、輸送の比較同型で移す。
規約：同じ指定変換と頂点を全時間で保つ既存の輸送を使う。
使われ方：comma 表示の局所相対普遍性を元の Kan 条件へ戻す。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：反転した圏の二頂点の同型は元の圏の同型へ戻る。
方針：逆向きの同型の辺を選び、反転を戻して可逆性を反映する。
規約：元の単体集合は quasicategory。
使われ方：反転した余錐の族の比較を余錐全体の関手同型へ戻す。 -/
def kanVertexIso_unop {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := X.op) (SSet.opObjEquiv.symm x) (SSet.opObjEquiv.symm y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y := by
  let a := Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective
    (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x) e.inv)
  have ha := Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective
    (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x) e.inv)
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk a)
    rw [ha]
    infer_instance
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edgeUnop (X := X) a) := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_op_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edgeUnop (X := X) a)).1
    exact hi
  exact asIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edgeUnop (X := X) a))

/-- 概要：指定された変換が U に関する相対左 Kan 拡張を与える点ごとの条件。
方針：各標準局所余錐の輸送後の余錐に標準 U 余極限性を課す。
規約：指定変換に両立する輸送を使い、境界充填性を定義に仮定しない。
使われ方：Kerodon §7.3.3（Tag 02Z2） の相対 Kan 条件と comma 上の組み立ての界面。 -/
def IsRelativeLeftKanExtension {K C D E : SSet.{u}} (U : D ⟶ E)
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D) (β : SSet.Homotopy F₀ (δ ≫ F)) : Prop :=
  ∀ c : C _⦋0⦌, ∃ t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport δ F₀ F β c, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U t.cocone

/-- 概要：同じ指定変換の二つの輸送の相対余極限性は同値。
方針：固定図式上の反転した余錐の族の同型を全余錐の関手同型に戻す。
規約：U は inner fibration、両値域は quasicategory とする。
使われ方：相対左 Kan 条件が局所輸送の選択に依存しないことの保証。 -/
lemma kanLeftTransport_isRelativeColimit_iff {K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) [InnerFibration U]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {β : SSet.Homotopy F₀ (δ ≫ F)} {c : C _⦋0⦌}
    (t s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport δ F₀ F β c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U t.cocone ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U s.cocone := by
  obtain ⟨e⟩ := t.coconeFamily_opIso s
  have e' := kanVertexIso_unop e
  have e'' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso t.cocone.val s.cocone.val :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e' (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) D)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c)))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_of_functorIso U _ _ e''

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
