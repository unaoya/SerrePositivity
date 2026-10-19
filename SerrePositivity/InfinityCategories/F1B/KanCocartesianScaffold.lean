module

public import SerrePositivity.InfinityCategories.F1B.KanUniversalScaffoldFiber

/-!
概要：quasicategory 値の図式から一般の cocartesian fibration への scaffold の条件。
方針：底上の可換性、水平辺の cocartesian 性、係数値からの fiber 同値を組み合わせる。
規約：Kan 値や left fibration への限定を含めない。
使われ方：Kerodon Definition 5.3.4.2 と一般の全空間比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：底の辺と始点係数の頂点が replacement の水平辺を定める。
方針：底の長さ一の射列に頂点の定値一単体を添える。
規約：係数方向の辺は定値である。
使われ方：scaffold が cocartesian 輸送を表すことの条件。 -/
def kanScaffoldHorizontalEdge {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {c d : C} (f : c ⟶ d) (x : (F.obj c) _⦋0⦌) :
    (simplicialReplacement F) _⦋1⦌ :=
  ⟨ComposableArrows.mk₁ f, SSet.const x⟩

/-- 概要：底を保つ replacement の射から係数値の fiber 比較を得る。
方針：定値の底の標準包含後の射を頂点 fiber へ持ち上げる。
規約：射影の充填性は定義には不要。
使われ方：一般の scaffold の係数値ごとの条件。 -/
def kanScaffoldFiberMap {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) (F : C ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) (c : C) :
    F.obj c ⟶ vertexFiber p (nerveVertex c) :=
  vertexFiberLift _ _ (simplicialReplacementConstantLift F c ≫ l) (by
    rw [Category.assoc, h, simplicialReplacementConstantLift_projection])

/-- 概要：inner fibration の頂点 fiber は quasicategory。
方針：fiber 内の内ホーンの充填性を使う。
規約：scaffold の同値条件を記述するための局所 instance。
使われ方：係数値と実際の fiber の同値の型。 -/
local instance {E B : SSet.{u}} (p : E ⟶ B) [InnerFibration p] (v : B _⦋0⦌) :
    Quasicategory (vertexFiber p v) := vertexFiber_quasicategory_of_innerFibration p v

/-- 概要：一般の cocartesian fibration への scaffold の条件。
方針：底、水平辺、各係数値の fiber 同値を独立に指定する。
規約：全空間比較の同値性を条件として仮定しない。
使われ方：Kerodon Definition 5.3.4.2、全空間比較の幾何的な入力。 -/
structure KanCocartesianScaffold {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [CocartesianFibration p]
    (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)]
    (l : simplicialReplacement F ⟶ E) : Prop where
  projection : l ≫ p = simplicialReplacementProjection F
  horizontal : ∀ {c d : C} (f : c ⟶ d) (x : (F.obj c) _⦋0⦌),
    IsCocartesianEdge p (l.app (Opposite.op ⦋1⦌) (kanScaffoldHorizontalEdge F f x))
  fiber : ∀ c, IsQCatEquivalence (kanScaffoldFiberMap p F l projection c)

/-- 概要：universal scaffold の水平辺の像は cocartesian。
方針：定値係数の族を一つの section に戻し、under の標準辺へ代入する。
規約：section の頂点条件だけを使うので射影の充填性は不要。
使われ方：一般の scaffold の水平辺の条件。 -/
lemma kanUniversalScaffold_horizontal {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) {c d : C} (f : c ⟶ d)
    (x : (kanCocartesianStrictTransport p c) _⦋0⦌) :
    IsCocartesianEdge p ((kanUniversalScaffold p).app (Opposite.op ⦋1⦌)
      (kanScaffoldHorizontalEdge (kanCocartesianStrictTransportDiagram p) f x)) := by
  change IsCocartesianEdge p (SSet.yonedaEquiv
    (kanUniversalScaffoldSimplex p ⟨ComposableArrows.mk₁ f, SSet.const x⟩))
  rw [kanUniversalScaffoldSimplex, kanCocartesianSectionsUncurry_const,
    ← Category.assoc, CartesianMonoidalCategory.lift_fst, SSet.yonedaEquiv_comp]
  rw [Equiv.apply_symm_apply]
  exact kanCocartesianSections_vertex p _ x _

/-- 概要：一般の cocartesian fibration の universal scaffold は全ての scaffold 条件を満たす。
方針：底の可換性、水平辺の性質、恒等射での評価同値を束ねる。
規約：全空間の前合成同値は別の比較定理で証明する。
使われ方：Kerodon Proposition 5.3.4.8、一般の復元の入力。 -/
lemma kanUniversalScaffold_isCocartesianScaffold
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [CocartesianFibration p] :
    KanCocartesianScaffold p (kanCocartesianStrictTransportDiagram p) (kanUniversalScaffold p) := by
  refine ⟨kanUniversalScaffold_projection p, kanUniversalScaffold_horizontal p, fun c ↦ ?_⟩
  have he : kanScaffoldFiberMap p (kanCocartesianStrictTransportDiagram p) (kanUniversalScaffold p)
      (kanUniversalScaffold_projection p) c = kanCocartesianStrictTransportEvaluate p c := by
    apply vertexFiber_hom_ext
    exact simplicialReplacementConstantLift_kanUniversalScaffold p c
  rw [he]
  exact kanCocartesianStrictTransportEvaluate_isQCatEquivalence p c

end SerrePositivity.InfinityCategories
