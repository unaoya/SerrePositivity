module

public import SerrePositivity.InfinityCategories.F2.Idempotent.ColimitRetracts
public import SerrePositivity.InfinityCategories.F2.Idempotent.DiagramOppositeRetracts

/-!
概要：冪等完備な元の ∞ 圏では、全図式の元の retract も極限を持つ。
方針：元の反転図式の retract と全余極限の存在の閉性を適用して戻す。
規約：添字は任意。新しい極限の存在を入力に仮定しない。
使われ方：完備化の新しい辺の fiber の存在の移送。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 冪等完備な元の圏内で、極限を持つ全図式の元の retract も極限を持つ。 -/
lemma hasLimit_of_diagram_retract {K X : SSet.{u}} [Quasicategory X]
    (hX : IsIdempotentComplete X) (a b : K ⟶ X)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction (functorVertex a) (functorVertex b)) (hb : HasLimit b) :
    HasLimit a := by
  have hr := diagram_retract_op a b ⟨r⟩
  have hc := hasColimit_of_diagram_retract hX.op (SSet.opFunctor.map a)
    (SSet.opFunctor.map b) hr.some ((F1B.kanHasLimit_iff_hasColimit_op b).mp hb)
  exact (F1B.kanHasLimit_iff_hasColimit_op a).mpr hc

end SerrePositivity.InfinityCategories.F2.Idempotent
