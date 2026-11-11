module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceIntervalVertexIso

/-!
概要：可逆な円柱による関手の同型の判定。
方針：関手単体集合の同型を可逆区間からの射へ延長し、curry する。
規約：区間は直積の第二因子。
使われ方：Kerodon Lemma 4.6.4.25（Tag 01KV） の圏論的円柱による比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：可逆区間からの関手の族を端点で制限すると、その端点の関手頂点に一致する。
方針：unit を使う閉構造の同値で前合成を計算する。
規約：標的の quasicategory 性は不要。
使われ方：Kerodon §4.6.4（Tag 01KE） の円柱の端点の同定。 -/
lemma functorVertex_equivalenceCylinderEndpoint_uncurry {A X : SSet.{u}}
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ⟶ (ihom A).obj X) (b : Bool) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A b ≫ uncurry G) =
      G.app (Opposite.op ⦋0⦌) (nerveEquiv.symm (Codiscrete.mk (ULift.up b))) := by
  have hh : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A b ≫ uncurry G =
      uncurry' (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalPoint b ≫ G) := by
    rw [uncurry', uncurry_natural_left]
    rfl
  rw [hh]
  change SSet.unitHomEquiv _ (curry' (uncurry' (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalPoint b ≫ G))) = _
  rw [curry'_uncurry']
  rfl

/-- 概要：同型な二つの関手は可逆な円柱上の一つの族へ延長できる。
方針：関手単体集合の頂点の同型を可逆区間へ延長して uncurry する。
規約：標的 X は quasicategory、A は任意。
使われ方：Kerodon Lemma 4.6.4.25（Tag 01KV） の円柱の構成。 -/
lemma exists_equivalenceCylinder_extension_of_functorIso {A X : SSet.{u}}
    [Quasicategory X] {f g : A ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) :
    ∃ H : A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ⟶ X,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A false ≫ H = f ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A true ≫ H = g := by
  obtain ⟨G, hG₀, hG₁⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.exists_equivalenceInterval_map_of_vertexIso e
  refine ⟨uncurry G, ?_, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
    rw [functorVertex_equivalenceCylinderEndpoint_uncurry]
    exact hG₀
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
    rw [functorVertex_equivalenceCylinderEndpoint_uncurry]
    exact hG₁

/-- 概要：二つの関手を可逆な円柱上へ延長できれば両者は同型。
方針：可逆区間の二頂点の同型を curry した族で写す。
規約：関手単体集合の同型の存在を結論とする。
使われ方：Kerodon Lemma 4.6.4.25（Tag 01KV） の円柱による同型判定。 -/
lemma nonempty_functorIso_of_equivalenceCylinder_extension {A X : SSet.{u}}
    [Quasicategory X] {f g : A ⟶ X} (H : A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ⟶ X)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A false ≫ H = f)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A true ≫ H = g) : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) := by
  let x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval.{u} _⦋0⦌ := nerveEquiv.symm (Codiscrete.mk (ULift.up false))
  let y : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval.{u} _⦋0⦌ := nerveEquiv.symm (Codiscrete.mk (ULift.up true))
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isContractibleKan_codiscreteNerve (ULift.{u} Bool)
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso (hc.isTerminalVertex x) (hc.isTerminalVertex y)
  have hx : (curry H).app (Opposite.op ⦋0⦌) x = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f := by
    rw [← functorVertex_equivalenceCylinderEndpoint_uncurry, uncurry_curry, h₀]
  have hy : (curry H).app (Opposite.op ⦋0⦌) y = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g := by
    rw [← functorVertex_equivalenceCylinderEndpoint_uncurry, uncurry_curry, h₁]
  exact ⟨(eqToIso (congrArg SSet.HomotopyCategory.mk hx)).symm ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (curry H) ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk hy)⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
