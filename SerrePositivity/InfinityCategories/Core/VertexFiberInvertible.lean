module

public import SerrePositivity.InfinityCategories.Core.InnerFiber
public import SerrePositivity.InfinityCategories.Core.RelativeOuterHorn
public import SerrePositivity.InfinityCategories.Core.OuterHornConverse

/-!
概要：inner fibration の fiber 内の辺の可逆性の検出。
方針：元の quasicategory の可逆辺を使い、標的の定値単体上で外側ホーンを充填する。
規約：元の始域と標的に quasicategory 性を要求する。
使われ方：Kerodon §4.5.3 の固定図式上の自然同型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：inner fibration の fiber 内の辺は、元の始域で可逆であるとき、かつそのときに限り可逆。
方針：順方向は包含、逆方向は定値の標的上の相対外側ホーンの充填で示す。
規約：p は inner fibration、元の始域・標的は quasicategory。
使われ方：Kerodon §4.5.3 の fiber 内のホモトピーの可逆性。 -/
lemma isInvertibleEdge_vertexFiber_iff {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [InnerFibration p]
    (b : B _⦋0⦌) {x y : (vertexFiber p b) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (vertexFiber p b)) x y) :
    IsInvertibleEdge e ↔ IsInvertibleEdge (e.map ((truncation 2).map (vertexFiberι p b))) := by
  constructor
  · intro he
    exact he.map _
  · intro he
    apply isInvertibleEdge_of_hasFinalHornFillers e
    intro n σ hσ
    have hw : (σ ≫ vertexFiberι p b) ≫ p =
        (horn (n + 2) (Fin.last (n + 2))).ι ≫ SSet.const b := by
      rw [Category.assoc, vertexFiberι_comp, SSet.comp_const, SSet.comp_const]
    have hEdge : IsInvertibleEdge (edgeOfSimplex
        ((σ ≫ vertexFiberι p b).app (Opposite.op ⦋1⦌) (finalHornEdge n))) := by
      have hh := congrArg ((vertexFiberι p b).app (Opposite.op ⦋1⦌)) hσ
      exact (isInvertibleEdge_congr hh).2 he
    obtain ⟨F, hF, hFp⟩ := innerFibration_lift_finalHorn p n (σ ≫ vertexFiberι p b)
      (SSet.const b) hw hEdge
    refine ⟨vertexFiberLift p b F hFp, ?_⟩
    apply vertexFiber_hom_ext p b
    rw [Category.assoc, vertexFiberLift_ι]
    exact hF

end SerrePositivity.InfinityCategories
