module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFiberMaps

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.UniversalScaffoldFiber
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：quasicategory 値の図式から一般の cocartesian fibration への scaffold の条件。
方針：底上の可換性、水平辺の cocartesian 性、係数値からの fiber 同値を組み合わせる。
規約：Kan 値や left fibration への限定を含めない。
使われ方：Kerodon Definition 5.3.4.2（Tag 0255） と一般の全空間比較。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：底の辺と始点係数の頂点が replacement の水平辺を定める。
方針：底の長さ一の射列に頂点の定値一単体を添える。
規約：係数方向の辺は定値である。
使われ方：scaffold が cocartesian 輸送を表すことの条件。 -/
def cocartesianScaffoldHorizontalEdge {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {c d : C} (f : c ⟶ d) (x : (F.obj c) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F) _⦋1⦌ :=
  ⟨ComposableArrows.mk₁ f, SSet.const x⟩

/-- 概要：inner fibration の頂点 fiber は quasicategory。
方針：fiber 内の内ホーンの充填性を使う。
規約：scaffold の同値条件を記述するための局所 instance。
使われ方：係数値と実際の fiber の同値の型。 -/
local instance {E B : SSet.{u}} (p : E ⟶ B) [InnerFibration p] (v : B _⦋0⦌) :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p v) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiber_quasicategory_of_innerFibration p v

/-- 概要：一般の cocartesian fibration への scaffold の条件。
方針：底、水平辺、各係数値の fiber 同値を独立に指定する。
規約：全空間比較の同値性を条件として仮定しない。
使われ方：Kerodon Definition 5.3.4.2（Tag 0255）、全空間比較の幾何的な入力。 -/
structure CocartesianScaffold {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)]
    (l : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E) : Prop where
  projection : l ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F
  horizontal : ∀ {c d : C} (f : c ⟶ d) (x : (F.obj c) _⦋0⦌),
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (l.app (Opposite.op ⦋1⦌) (cocartesianScaffoldHorizontalEdge F f x))
  fiber : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldFiberMap p F l projection c)

/-- 概要：universal scaffold の水平辺の像は cocartesian。
方針：定値係数の族を一つの section に戻し、under の標準辺へ代入する。
規約：section の頂点条件だけを使うので射影の充填性は不要。
使われ方：一般の scaffold の水平辺の条件。 -/
lemma cocartesianUniversalScaffold_horizontal {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) {c d : C} (f : c ⟶ d)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransport p c) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold p).app (Opposite.op ⦋1⦌)
      (cocartesianScaffoldHorizontalEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p) f x)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianUniversalScaffoldSimplex p ⟨ComposableArrows.mk₁ f, SSet.const x⟩))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianUniversalScaffoldSimplex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsUncurry_const,
    ← Category.assoc, CartesianMonoidalCategory.lift_fst, SSet.yonedaEquiv_comp]
  rw [Equiv.apply_symm_apply]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections_vertex p _ x _

/-- 概要：一般の cocartesian fibration の universal scaffold は全ての scaffold 条件を満たす。
方針：底の可換性、水平辺の性質、恒等射での評価同値を束ねる。
規約：全空間の前合成同値は別の比較定理で証明する。
使われ方：Kerodon Proposition 5.3.4.8（Tag 0370）、一般の復元の入力。 -/
@[kerodon 0370, kerodon 0371]
lemma cocartesianUniversalScaffold_isCocartesianScaffold
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] :
    CocartesianScaffold p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold p) := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold_projection p, cocartesianUniversalScaffold_horizontal p, fun c ↦ ?_⟩
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldFiberMap p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold_projection p) c = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportEvaluate p c := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplicialReplacementConstantLift_kanUniversalScaffold p c
  rw [he]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportEvaluate_isQCatEquivalence p c

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
