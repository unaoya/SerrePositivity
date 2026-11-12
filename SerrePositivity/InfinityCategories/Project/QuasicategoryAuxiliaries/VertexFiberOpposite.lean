module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-! # 頂点上の fiber と反転

概要：頂点上の fiber を反転したものは反転した射の対応する fiber と同型である。
方針：各次数の部分型の値を opObjEquiv で移す。
規約：指定した頂点上の厳密な fiber。使われ方：fiber の始対象を反転した終対象へ移す。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：反転した頂点の定値単体は元の定値単体の反転。
方針：零次元への唯一の順序写像は反転しても同じである。
規約：全次数で成り立つ。使われ方：反転した fiber の固定条件。 -/
lemma stablePinchedConstant_op {X : SSet.{u}} (x : X _⦋0⦌) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := X.op) (SSet.opObjEquiv.symm x) n =
      SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x n) := by
  change X.map (SimplexCategory.rev.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0)).op x = _
  have hc : SimplexCategory.rev.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0) =
      SimplexCategory.const ⦋n⦌ ⦋0⦌ 0 := by
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    exact @Subsingleton.elim (Fin 1) inferInstance _ _
  rw [hc]
  rfl

/-- 概要：fiber を反転した単体と反転した射の fiber の単体は同値。
方針：部分型の値を反転し、定値単体の反転の式で条件を移す。
規約：各次数での厳密な同値。使われ方：fiber の反転同型。 -/
def vertexFiberOpEquiv {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    (d : SimplexCategoryᵒᵖ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b).op.obj d ≃
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (SSet.opFunctor.map p) (SSet.opObjEquiv.symm b)).obj d where
  toFun s := ⟨SSet.opObjEquiv.symm (SSet.opObjEquiv s).val, by
    rw [SSet.opFunctor_map, stablePinchedConstant_op]
    exact congrArg SSet.opObjEquiv.symm (SSet.opObjEquiv s).property⟩
  invFun s := SSet.opObjEquiv.symm (⟨SSet.opObjEquiv s.val, by
    have h := congrArg (SSet.opObjEquiv (X := B) (n := d)) s.property
    exact h.trans (congrArg (SSet.opObjEquiv (X := B) (n := d))
      (stablePinchedConstant_op b d.unop.len))⟩ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b).obj d)
  left_inv s := by
    apply (SSet.opObjEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) (n := d)).injective
    apply Subtype.ext
    rfl
  right_inv s := by apply Subtype.ext; rfl

/-- 概要：頂点上の fiber の反転と、反転した射の fiber は単体集合として同型。
方針：各次数の部分型の同値を束ねる。
規約：ファイブレーション性は不要。使われ方：相対始対象の境界充填の双対化。 -/
def vertexFiberOpIso {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b).op ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (SSet.opFunctor.map p) (SSet.opObjEquiv.symm b) :=
  NatIso.ofComponents (fun d => (vertexFiberOpEquiv p b d).toIso) (fun _ => by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    rfl)

/-- 概要：fiber の始対象は反転した射の fiber の終対象を与える。
方針：始対象の反転と fiber の反転同型を使う。
規約：quasicategory 性は不要。使われ方：相対終対象の定理への入力。 -/
lemma IsInitialVertex.isTerminalVertex_opFiber {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    {x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((vertexFiberOpIso p b).hom.app (Opposite.op ⦋0⦌) (SSet.opObjEquiv.symm x)) :=
  hx.op_isTerminalVertex.map_of_isIso (vertexFiberOpIso p b).hom

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex export _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsInitialVertex (isTerminalVertex_opFiber)


end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
