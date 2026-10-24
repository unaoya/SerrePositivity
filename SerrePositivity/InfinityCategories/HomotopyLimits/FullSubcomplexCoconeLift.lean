module

public import SerrePositivity.InfinityCategories.HomotopyLimits.JoinVertexSummands
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeCoconeAbsolute
public import SerrePositivity.InfinityCategories.Core.FullSubcomplexFibration

/-!
概要：全部分複体の元の図式の周囲の余錐を、元の頂点条件だけで内部の余錐へ制限する。
方針：join の全頂点を元の底図式と元の余錐頂点に分け、同じ全写像を持ち上げる。
規約：元の図式・余錐の全一単体と高次単体を保持する。余極限性は仮定しない。
使われ方：実際の sifted 前層余極限余錐を P_Σ 内へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {K X : SSet.{u}} (P : X _⦋0⦌ → Prop)
  (r : K ⟶ (fullSubcomplexOnVertices X P : SSet.{u}))
  (q : JoinCocone (r ≫ (fullSubcomplexOnVertices X P).ι))

/-- 元の頂点が所属すれば、周囲の同じ余錐の全頂点が元の部分複体に所属する。 -/
lemma fullSubcomplexCocone_vertices (hq : P q.vertex) :
    ∀ v, P (q.val.app (Opposite.op ⦋0⦌) v) := by
  intro v
  obtain ⟨b, rfl⟩ | ⟨a, rfl⟩ := joinVertexSummands v
  · have H := congrArg (fun f => f.app (Opposite.op ⦋0⦌) b) q.property
    change q.val.app _ ((joinInl K Δ[0]).app _ b) = (r.app _ b).val at H
    rw [H]
    exact fullSubcomplexOnVertices_vertex (r.app _ b)
  · have hr : joinInr K (Δ[0] : SSet.{u}) ≫ q.val = SSet.const q.vertex := by
      rw [← SSet.yonedaEquiv_symm_zero q.vertex]
      exact (SSet.yonedaEquiv.symm_apply_apply (joinInr K Δ[0] ≫ q.val)).symm
    have H := congrArg (fun f => f.app (Opposite.op ⦋0⦌) a) hr
    change q.val.app _ ((joinInr K Δ[0]).app _ a) = PinchedHom.constant q.vertex 0 at H
    rw [H, pinchedConstant_zero]
    exact hq

/-- 元の周囲の全余錐を、元の同じ図式上の内部余錐として保持する。 -/
def fullSubcomplexCoconeLift (hq : P q.vertex) : JoinCocone r := by
  refine ⟨fullSubcomplexLift P q.val (fullSubcomplexCocone_vertices P r q hq), ?_⟩
  apply (cancel_mono (fullSubcomplexOnVertices X P).ι).1
  rw [Category.assoc, fullSubcomplexLift_ι]
  exact q.property

/-- 同じ持ち上げ余錐を包含すると、元の周囲の全余錐を厳密に回収する。 -/
lemma fullSubcomplexCoconeLift_inclusion (hq : P q.vertex) :
    F1B.kanPostcomposeCocone (fullSubcomplexOnVertices X P).ι
      (fullSubcomplexCoconeLift P r q hq) = q := by
  apply Subtype.ext
  exact fullSubcomplexLift_ι P q.val (fullSubcomplexCocone_vertices P r q hq)

end SerrePositivity.InfinityCategories.HomotopyLimits
