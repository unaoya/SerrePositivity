module

public import SerrePositivity.InfinityCategories.F1.UniversalScaffold
public import SerrePositivity.InfinityCategories.F1.SimplicialReplacementFiberKan

/-!
概要：universal scaffold の頂点 fiber 上の射と恒等射評価との同定。
方針：定値射列の under への持ち上げを恒等射に同定し、対角評価を頂点評価に戻す。
規約：まず射の等式を示し、left fibration 性は評価の同値性にのみ使う。
使われ方：Kerodon Proposition 5.3.4.8、universal scaffold の fiber 条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：定値射列の under への標準持ち上げは恒等射に定値。
方針：定値関手の全ての射が恒等射であることを計算する。
規約：任意の次元の定値射列を扱う。
使われ方：Kerodon Proposition 5.3.4.8、fiber 上の対角評価の簡約。 -/
lemma scaffoldUnderChain_constant {C : Type u} [Category.{u} C] (c : C) (n : ℕ) :
    scaffoldUnderChain ((CategoryTheory.Functor.const (Fin (n + 1))).obj c) =
      (CategoryTheory.Functor.const (Fin (n + 1))).obj (Under.mk (𝟙 c)) := rfl

/-- 概要：定値の底における universal scaffold は恒等射での strict transport 評価。
方針：対角の第一成分が恒等射の定値頂点であることと curry の頂点評価を使う。
規約：元の全空間への射の等式として述べる。
使われ方：Kerodon Proposition 5.3.4.8、fiber 比較を既存の評価へ帰着する式。 -/
lemma simplicialReplacementConstantLift_universalScaffold
    {C : Type u} [Category.{u} C] {E : SSet.{u}} (p : E ⟶ nerve C) (c : C) :
    simplicialReplacementConstantLift (leftStrictTransportDiagram p) c ≫ universalScaffold p =
      leftStrictTransportEvaluate p c ≫ vertexFiberι p (nerveVertex c) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  let f : (Δ[d.unop.len] : SSet.{u}) ⟶ leftStrictTransport p c := SSet.yonedaEquiv.symm s
  have ht : universalScaffoldSimplex p
      (⟨(CategoryTheory.Functor.const (Fin (d.unop.len + 1))).obj c, f⟩) =
      f ≫ leftStrictTransportEvaluate p c ≫ vertexFiberι p (nerveVertex c) := by
    rw [universalScaffoldSimplex, scaffoldUnderChain_constant]
    have he := curry_evaluateFunctorAt_vertex (relativeFunctorUncurry f)
      (strictTransportUnderIdentityVertex c)
    change curry (uncurry (f ≫ vertexFiberι _ _)) ≫ _ = _ at he
    rw [curry_uncurry] at he
    exact he.symm
  change SSet.yonedaEquiv (universalScaffoldSimplex p
      (⟨(CategoryTheory.Functor.const (Fin (d.unop.len + 1))).obj c, f⟩)) = _
  rw [ht, SSet.yonedaEquiv_comp]
  change _ = (leftStrictTransportEvaluate p c ≫ vertexFiberι p (nerveVertex c)).app d s
  simp only [f, Equiv.apply_symm_apply]

/-- 概要：universal scaffold が誘導する頂点 fiber 間の射。
方針：元の fiber の包含を評価射と合成し、底上の可換性で標的の fiber に持ち上げる。
規約：全空間の同値性はここでは仮定しない。
使われ方：Kerodon Proposition 5.3.4.8、fiber ごとの比較射。 -/
def universalScaffoldFiberMap {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) (c : C) :
    vertexFiber (simplicialReplacementProjection (leftStrictTransportDiagram p)) (nerveVertex c) ⟶
      vertexFiber p (nerveVertex c) :=
  vertexFiberLift _ _ (vertexFiberι _ _ ≫ universalScaffold p) (by
    rw [Category.assoc, universalScaffold_projection, vertexFiberι_comp])

/-- 概要：係数値からの標準 fiber 同型を通すと universal scaffold は恒等射評価に一致する。
方針：fiber の包含後に定値の底の評価の等式を使う。
規約：係数図式は p の strict transport。
使われ方：Kerodon Proposition 5.3.4.8、fiber 条件に既存の評価の結果を適用する式。 -/
lemma simplicialReplacementFiberMap_universalScaffoldFiberMap
    {C : Type u} [Category.{u} C] {E : SSet.{u}} (p : E ⟶ nerve C) (c : C) :
    simplicialReplacementFiberMap (leftStrictTransportDiagram p) c ≫
      universalScaffoldFiberMap p c = leftStrictTransportEvaluate p c := by
  apply vertexFiber_hom_ext
  exact simplicialReplacementConstantLift_universalScaffold p c

/-- 概要：universal scaffold の fiber 射は trivial Kan fibration。
方針：係数値との標準同型の逆と恒等射評価との合成で表し、全境界の持ち上げ性を移す。
規約：p の left fibration 性は恒等射評価の持ち上げ性に使う。
使われ方：Kerodon Proposition 5.3.4.8、fiber の同値と選択空間の可縮性。 -/
instance universalScaffoldFiberMap_trivialKanFibration
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C) :
    TrivialKanFibration (universalScaffoldFiberMap p c) := by
  have h := simplicialReplacementFiberMap_universalScaffoldFiberMap p c
  have he : universalScaffoldFiberMap p c =
      inv (simplicialReplacementFiberMap (leftStrictTransportDiagram p) c) ≫
        leftStrictTransportEvaluate p c := by
    rw [← h, IsIso.inv_hom_id_assoc]
  rw [he]
  exact ⟨trivialKanFibrations.comp_mem _ _ TrivialKanFibration.mem TrivialKanFibration.mem⟩

/-- 概要：strict transport の simplicial replacement の頂点 fiber は Kan 複体。
方針：strict transport の係数値の Kan 性を標準 fiber 比較で移す。
規約：simplicial replacement の全空間には充填性を主張しない。
使われ方：Kerodon Proposition 5.3.4.8、fiber の圏同値を述べるための始域の構造。 -/
instance leftStrictTransportReplacementFiber_kanComplex
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C) :
    KanComplex (vertexFiber
      (simplicialReplacementProjection (leftStrictTransportDiagram p)) (nerveVertex c)) := by
  have : KanComplex ((leftStrictTransportDiagram p).obj c) := leftStrictTransport_kanComplex p c
  exact simplicialReplacementFiber_kanComplex (leftStrictTransportDiagram p) c

/-- 概要：universal scaffold の fiber 射は圏同値。
方針：両側の fiber の Kan 性を確認し、trivial Kan fibration の同値判定を適用する。
規約：全空間の同値性はまだ結論に含めない。
使われ方：Kerodon Proposition 5.3.4.8、universal scaffold の fiber 条件。 -/
lemma universalScaffoldFiberMap_isQCatEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C) :
    IsQCatEquivalence (universalScaffoldFiberMap p c) := by
  have : KanComplex ((leftStrictTransportDiagram p).obj c) := leftStrictTransport_kanComplex p c
  have := vertexFiber_kanComplex_of_leftFibration p (nerveVertex c)
  exact isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories
