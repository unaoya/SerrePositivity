module

public import SerrePositivity.InfinityCategories.Core.LimitConeFamily
public import SerrePositivity.InfinityCategories.Core.RelativeTerminalExtension

/-!
概要：相対終点境界充填から fiber の終対象と極限錐を得る。
方針：標的が定値の境界充填問題に制限する。
規約：逆方向は追加の構造を必要とするためこの補題には含めない。
使われ方：Kerodon §7.1.5・7.1.6 の相対終対象から極限への方向。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：射の上で終点境界を充填できる頂点は、その fiber の終対象。
方針：fiber の境界を元へ含め、標的の単体を定値に取る。
規約：quasicategory 性・inner fibration 性は不要。
使われ方：Kerodon §7.1.5 の相対終対象の fiber への制限。 -/
lemma TerminalBoundaryLifting.isTerminalVertex_fiber {E B : SSet.{u}}
    (p : E ⟶ B) (b : B _⦋0⦌) (x : (vertexFiber p b) _⦋0⦌)
    (hx : TerminalBoundaryLifting p x.val) : IsTerminalVertex x := by
  intro n a ha
  have hend : boundaryVertex n (Fin.last (n + 1)) ≫ (a ≫ vertexFiberι p b) =
      SSet.yonedaEquiv.symm x.val := by
    rw [← Category.assoc, ha, SSet.yonedaEquiv_symm_comp]
    rfl
  have sq : CommSq (a ≫ vertexFiberι p b) (boundary (n + 1)).ι p (SSet.const b) := by
    constructor
    rw [Category.assoc, vertexFiberι_comp, SSet.comp_const, SSet.comp_const]
  obtain ⟨F, hF, hFp⟩ := hx n _ _ hend sq
  refine ⟨vertexFiberLift p b F hFp, ?_⟩
  apply vertexFiber_hom_ext p b
  rw [Category.assoc, vertexFiberLift_ι]
  exact hF

/-- 概要：錐の制限射の上で終点境界を充填できる錐は極限錐。
方針：固定図式上の fiber の終対象性へ制限し、slice との比較で戻す。
規約：X は quasicategory、添字 K は任意。
使われ方：Kerodon Proposition 7.1.6.13 の絶対極限での一方向。 -/
lemma isLimitCone_of_terminalBoundaryLifting_coneRestriction
    {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (c : JoinCone p)
    (hc : TerminalBoundaryLifting (coneRestriction K X) (functorVertex c.val)) : IsLimitCone c := by
  apply (isLimitCone_iff_isTerminalVertex_coneFamily c).2
  exact TerminalBoundaryLifting.isTerminalVertex_fiber (coneRestriction K X) (functorVertex p)
    (coneFamilyVertexEquiv p c) hc

end SerrePositivity.InfinityCategories
