module

public import SerrePositivity.InfinityCategories.F1B.KanUniversalScaffold
public import SerrePositivity.InfinityCategories.F1B.KanCocartesianStrictTransportEquivalence
public import SerrePositivity.InfinityCategories.F1.Diagrams.SimplicialReplacementFiber

/-!
概要：cocartesian universal scaffold の fiber 比較を恒等射評価と同定する。
方針：定値射列の under の単体を恒等射の定値単体へ戻す。
規約：replacement の全空間の quasicategory 性を仮定しない。
使われ方：一般の scaffold の fiber 条件と全空間比較の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories

/-- 概要：定値射列の under への標準持ち上げは恒等射に定値。
方針：定値関手の全ての射が恒等射であることを計算する。
規約：元の圏の対象 c と次数 n は任意。
使われ方：fiber 上の対角評価の簡約。 -/
lemma kanScaffoldUnderChain_constant {C : Type u} [Category.{u} C] (c : C) (n : ℕ) :
    scaffoldUnderChain ((CategoryTheory.Functor.const (Fin (n + 1))).obj c) =
      (CategoryTheory.Functor.const (Fin (n + 1))).obj (Under.mk (𝟙 c)) := rfl

/-- 概要：係数値の標準包含を評価すると恒等射での評価になる。
方針：定値の底の under 単体を評価点に直し、族の評価公式を使う。
規約：元の全空間 E への射の等式。
使われ方：universal scaffold の fiber 条件を既存の同値へ帰着する。 -/
lemma simplicialReplacementConstantLift_kanUniversalScaffold
    {C : Type u} [Category.{u} C] {E : SSet.{u}} (p : E ⟶ nerve C) (c : C) :
    simplicialReplacementConstantLift (kanCocartesianStrictTransportDiagram p) c ≫
        kanUniversalScaffold p =
      kanCocartesianStrictTransportEvaluate p c ≫ vertexFiberι p (nerveVertex c) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  let f : (Δ[d.unop.len] : SSet.{u}) ⟶ kanCocartesianStrictTransport p c :=
    SSet.yonedaEquiv.symm s
  have ht : kanUniversalScaffoldSimplex p
      (⟨(CategoryTheory.Functor.const (Fin (d.unop.len + 1))).obj c, f⟩) =
      f ≫ kanCocartesianStrictTransportEvaluate p c ≫ vertexFiberι p (nerveVertex c) := by
    rw [kanUniversalScaffoldSimplex, kanScaffoldUnderChain_constant]
    exact kanCocartesianSectionsUncurry_evaluate f (nerveVertex (Under.mk (𝟙 c)))
  change SSet.yonedaEquiv (kanUniversalScaffoldSimplex p
      (⟨(CategoryTheory.Functor.const (Fin (d.unop.len + 1))).obj c, f⟩)) = _
  rw [ht, SSet.yonedaEquiv_comp]
  change _ = (kanCocartesianStrictTransportEvaluate p c ≫ vertexFiberι p (nerveVertex c)).app d s
  simp only [f, Equiv.apply_symm_apply]

/-- 概要：universal scaffold が誘導する実際の頂点 fiber 間の射。
方針：底上の可換性により、元の fiber の包含後の評価を持ち上げる。
規約：射影の充填性は構成には不要。
使われ方：各 fiber の同値性と、全空間比較の仮定。 -/
def kanUniversalScaffoldFiberMap {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) (c : C) :
    vertexFiber (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p))
        (nerveVertex c) ⟶ vertexFiber p (nerveVertex c) :=
  vertexFiberLift _ _ (vertexFiberι _ _ ≫ kanUniversalScaffold p) (by
    rw [Category.assoc, kanUniversalScaffold_projection, vertexFiberι_comp])

/-- 概要：標準 fiber 同型で戻すと universal scaffold の fiber 射は恒等射評価。
方針：fiber 包含後の等式で判定する。
規約：射の厳密な等式。
使われ方：fiber 評価の全境界持ち上げを移送する。 -/
lemma simplicialReplacementFiberMap_kanUniversalScaffoldFiberMap
    {C : Type u} [Category.{u} C] {E : SSet.{u}} (p : E ⟶ nerve C) (c : C) :
    simplicialReplacementFiberMap (kanCocartesianStrictTransportDiagram p) c ≫
      kanUniversalScaffoldFiberMap p c = kanCocartesianStrictTransportEvaluate p c := by
  apply vertexFiber_hom_ext
  exact simplicialReplacementConstantLift_kanUniversalScaffold p c

/-- 概要：cocartesian universal scaffold の各 fiber の比較は自明 Kan fibration。
方針：標準 fiber 同型の逆と恒等射での評価に分解する。
規約：p は一般の cocartesian fibration。
使われ方：universal scaffold の全空間比較の fiber 条件。 -/
instance kanUniversalScaffoldFiberMap_trivialKanFibration
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [CocartesianFibration p] (c : C) :
    TrivialKanFibration (kanUniversalScaffoldFiberMap p c) := by
  have h := simplicialReplacementFiberMap_kanUniversalScaffoldFiberMap p c
  have he : kanUniversalScaffoldFiberMap p c =
      inv (simplicialReplacementFiberMap (kanCocartesianStrictTransportDiagram p) c) ≫
        kanCocartesianStrictTransportEvaluate p c := by
    rw [← h, IsIso.inv_hom_id_assoc]
  rw [he]
  exact ⟨trivialKanFibrations.comp_mem _ _ TrivialKanFibration.mem TrivialKanFibration.mem⟩

/-- 概要：quasicategory 値の replacement の頂点 fiber は quasicategory。
方針：標準 fiber 同型で内ホーンを係数値へ移して充填する。
規約：係数値の Kan 性と全空間の充填性は要求しない。
使われ方：一般の scaffold の fiber 間の ∞ 圏同値を述べる。 -/
instance kanSimplicialReplacementFiber_quasicategory {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) [Quasicategory (F.obj c)] :
    Quasicategory (vertexFiber (simplicialReplacementProjection F) (nerveVertex c)) where
  hornFilling' {n i} a h₀ hn := by
    let e := asIso (simplicialReplacementFiberMap F c)
    obtain ⟨H, hH⟩ := Quasicategory.hornFilling h₀ hn (a ≫ e.inv)
    refine ⟨H ≫ e.hom, ?_⟩
    rw [← Category.assoc, ← hH, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 概要：元の射影の頂点 fiber は quasicategory。
方針：inner fibration の fiber の充填性を使う。
規約：このファイルで同値の型を述べるための局所 instance。
使われ方：universal scaffold の fiber の ∞ 圏同値。 -/
local instance {E B : SSet.{u}} (p : E ⟶ B) [InnerFibration p] (v : B _⦋0⦌) :
    Quasicategory (vertexFiber p v) := vertexFiber_quasicategory_of_innerFibration p v

/-- 概要：universal scaffold の実際の fiber 射は ∞ 圏の同値。
方針：両側の fiber の quasicategory 性を確認して自明 Kan fibration の同値判定を使う。
規約：全空間の同値性はまだ主張しない。
使われ方：scaffold の比較定理への fiber 条件の入力。 -/
lemma kanUniversalScaffoldFiberMap_isQCatEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [CocartesianFibration p] (c : C) :
    IsQCatEquivalence (kanUniversalScaffoldFiberMap p c) := by
  have : Quasicategory ((kanCocartesianStrictTransportDiagram p).obj c) :=
    kanCocartesianStrictTransport_quasicategory p c
  exact isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories
