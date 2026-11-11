module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.OppositeFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap

/-!
概要：単体集合の反転と頂点 fiber の厳密な同型。
方針：各次数の部分型を反転の全単射で対応させ、零単体への射の一意性で定値条件を移す。
規約：Kan 性や fibration 性は要求しない。
使われ方：HTT 4.2.4.1、元の比較射と反転比較射の導来 fiber の直接の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 概要：頂点の定値単体は単体集合の反転と可換。
方針：零単体への唯一の順序写像の反転が同じ写像であることを使う。
規約：頂点は反転の零次全単射で移す。
使われ方：反転した頂点 fiber の固定条件の照合。 -/
lemma opposite_pinchedConstant {B : SSet.{u}} (b : B _⦋0⦌) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SSet.opObjEquiv.symm b : B.op _⦋0⦌) n =
      SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b n) := by
  change SSet.opObjEquiv.symm (B.map
    (SimplexCategory.rev.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0)).op b) = _
  have h : SimplexCategory.rev.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0) =
      SimplexCategory.const ⦋n⦌ ⦋0⦌ 0 := by
    ext i
    simp
  rw [h]
  rfl

/-- 概要：頂点 fiber の反転は反転した射の同じ頂点の fiber と厳密に同型。
方針：各次数の反転の全単射で元と固定条件を移し、自然性は元の引き戻しを使う。
規約：底の頂点は零次の反転の全単射で移す。
使われ方：反転した path 置換の strict fiber と元の導来 fiber の比較。 -/
def oppositeVertexFiberIso {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b).op ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (SSet.opFunctor.map p) (SSet.opObjEquiv.symm b) :=
  NatIso.ofComponents (fun d ↦ Equiv.toIso {
    toFun a := ⟨SSet.opObjEquiv.symm (SSet.opObjEquiv a).val, by
      change SSet.opObjEquiv.symm (p.app d (SSet.opObjEquiv a).val) = _
      exact (congrArg (fun z : B.obj d ↦ SSet.opObjEquiv.symm z)
        (SSet.opObjEquiv a).property).trans (opposite_pinchedConstant b d.unop.len).symm⟩
    invFun a := SSet.opObjEquiv.symm ⟨SSet.opObjEquiv a.val, by
      have h := a.property
      change SSet.opObjEquiv.symm (p.app d (SSet.opObjEquiv a.val)) = _ at h
      exact SSet.opObjEquiv.symm.injective
        (h.trans (opposite_pinchedConstant b d.unop.len))⟩
    left_inv _ := rfl
    right_inv _ := rfl }) (by
      intro d e α
      apply ConcreteCategory.hom_ext
      intro a
      rfl)

/-- 概要：頂点 fiber の反転の同型は元の全空間への包含と厳密に可換。
方針：各次数で部分型の値の反転を計算する。
規約：元の包含も反転して比較する。
使われ方：導来 fiber の反転比較の全空間の座標の保持。 -/
lemma oppositeVertexFiberIso_hom_ι {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (oppositeVertexFiberIso p b).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (SSet.opFunctor.map p) (SSet.opObjEquiv.symm b) =
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) := rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
