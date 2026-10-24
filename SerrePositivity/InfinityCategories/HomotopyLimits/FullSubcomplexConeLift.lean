module

public import SerrePositivity.InfinityCategories.HomotopyLimits.JoinVertexSummands
public import SerrePositivity.InfinityCategories.Core.EquivalenceLimits
public import SerrePositivity.InfinityCategories.Core.FullSubcomplexFibration

/-!
概要：全部分複体の元の図式の周囲の錐を、元の頂点条件だけで内部の錐へ制限する。
方針：join の全頂点を元の底図式と元の錐頂点に分け、同じ全写像を持ち上げる。
規約：元の図式・錐の全一単体と高次単体を保持する。余極限性は仮定しない。
使われ方：実際の sifted 前層余極限錐を 反映部分圏 内へ戻す。
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
  (q : JoinCone (r ≫ (fullSubcomplexOnVertices X P).ι))

/-- 概要：極限候補の頂点の所属から全錐の全頂点の所属を回収する。
方針：join の二因子で頂点を分ける。
規約：空の図式も扱う。
使われ方：全部分錐の持ち上げ。 -/
lemma fullSubcomplexCone_vertices (hq : P q.vertex) :
    ∀ v, P (q.val.app (Opposite.op ⦋0⦌) v) := by
  intro v
  obtain ⟨a, rfl⟩ | ⟨b, rfl⟩ := joinVertexSummands v
  · have hr : joinInl (Δ[0] : SSet.{u}) K ≫ q.val = SSet.const q.vertex := by
      rw [← SSet.yonedaEquiv_symm_zero q.vertex]
      exact (SSet.yonedaEquiv.symm_apply_apply (joinInl Δ[0] K ≫ q.val)).symm
    have H := congrArg (fun f => f.app (Opposite.op ⦋0⦌) a) hr
    change q.val.app _ ((joinInl Δ[0] K).app _ a) = PinchedHom.constant q.vertex 0 at H
    rw [H, pinchedConstant_zero]
    exact hq
  · have H := congrArg (fun f => f.app (Opposite.op ⦋0⦌) b) q.property
    change q.val.app _ ((joinInr Δ[0] K).app _ b) = (r.app _ b).val at H
    rw [H]
    exact fullSubcomplexOnVertices_vertex (r.app _ b)

/-- 概要：周囲の全錐を同じ図式の内部錐へ持ち上げる。
方針：全頂点の所属で全部分複体へ持ち上げる。
規約：元の全写像を保持する。
使われ方：反映部分圏の極限構成。 -/
def fullSubcomplexConeLift (hq : P q.vertex) : JoinCone r := by
  refine ⟨fullSubcomplexLift P q.val (fullSubcomplexCone_vertices P r q hq), ?_⟩
  apply (cancel_mono (fullSubcomplexOnVertices X P).ι).1
  rw [Category.assoc, fullSubcomplexLift_ι]
  exact q.property

/-- 概要：持ち上げ錐の包含後の値を回収する。
方針：全部分持ち上げの包含公式を使う。
規約：元の全錐との厳密な等式。
使われ方：極限性の反映。 -/
lemma fullSubcomplexConeLift_inclusion (hq : P q.vertex) :
    mapJoinCone (fullSubcomplexOnVertices X P).ι
      (fullSubcomplexConeLift P r q hq) = q := by
  apply Subtype.ext
  exact fullSubcomplexLift_ι P q.val (fullSubcomplexCone_vertices P r q hq)

end SerrePositivity.InfinityCategories.HomotopyLimits
