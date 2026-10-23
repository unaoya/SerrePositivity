module

public import SerrePositivity.InfinityCategories.F1.Joins.CosliceUniversalPrismSection
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorFiberHom
public import SerrePositivity.InfinityCategories.Core.FullyFaithful

/-!
概要：標準区間族の持ち上げの終点を、同じ恒等点を持つ実際の大域射と比較する。
方針：恒等錐での評価から相対関手空間の頂点同型を戻し、同じ同型を fiber へ制限する。
規約：fiber ごとに逆同値を選ばず、一つの大域的な相対頂点同型を使う。
使われ方：Hom 関手の大域比較の実際の fiber 作用を標準輸送へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 恒等錐で同じ値を持つ大域射は、同じ底を固定する相対関手空間で頂点同型を持つ。 -/
def leftFibrationCosliceMaps_vertexIso {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌)
    (f g : sliceUnder (SSet.yonedaEquiv.symm b) ⟶ E)
    (hf : f ≫ p = sliceUnderProjection (SSet.yonedaEquiv.symm b))
    (hg : g ≫ p = sliceUnderProjection (SSet.yonedaEquiv.symm b))
    (h : f.app (Opposite.op ⦋0⦌) (cosliceIdentityCone b) =
      g.app (Opposite.op ⦋0⦌) (cosliceIdentityCone b)) :
    VertexIso (relativeFunctorVertex p _ f hf) (relativeFunctorVertex p _ g hg) := by
  let vf := relativeFunctorVertex p _ f hf
  let vg := relativeFunctorVertex p _ g hg
  have he : (leftFibrationCoslicePointEvaluate p b).app (Opposite.op ⦋0⦌) vf =
      (leftFibrationCoslicePointEvaluate p b).app (Opposite.op ⦋0⦌) vg := by
    apply Subtype.ext
    have hE := leftFibrationCoslicePointEvaluate_ι p b
    have hF := congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌) vf) hE
    have hG := congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌) vg) hE
    change _ = (evaluateFunctorAt (cosliceIdentityCone b)).app (Opposite.op ⦋0⦌)
      (functorVertex f) at hF
    change _ = (evaluateFunctorAt (cosliceIdentityCone b)).app (Opposite.op ⦋0⦌)
      (functorVertex g) at hG
    rw [evaluateFunctorAt_functorVertex] at hF hG
    exact hF.trans (h.trans hG.symm)
  let e := leftFibrationCoslicePointEvaluate_equalIso p b
    (f := (SSet.const vf : (Δ[0] : SSet.{u}) ⟶ _)) (g := SSet.const vg)
    (by rw [SSet.const_comp, SSet.const_comp, he])
  have h₀ := e.app (stdSimplex.obj₀Equiv.symm 0)
  change VertexIso (PinchedHom.constant vf 0) (PinchedHom.constant vg 0) at h₀
  simpa only [PinchedHom.constant_zero] using h₀

/-- 普遍区間の持ち上げの終点と指定大域射の比較は、一つの相対頂点同型。 -/
def cosliceUniversalPrismLiftEndpoint_compareIso
    {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌) (d : E _⦋0⦌)
    (hd : p.app (Opposite.op ⦋0⦌) d = b)
    (f : sliceUnder (SSet.yonedaEquiv.symm b) ⟶ E)
    (hf : f ≫ p = sliceUnderProjection (SSet.yonedaEquiv.symm b))
    (h : f.app (Opposite.op ⦋0⦌) (cosliceIdentityCone b) = d) :
    VertexIso
      (relativeFunctorVertex p _ (cosliceUniversalPrismLiftEndpoint p b d hd)
        (cosliceUniversalPrismLiftEndpoint_projection p b d hd))
      (relativeFunctorVertex p _ f hf) :=
  leftFibrationCosliceMaps_vertexIso p b _ _ _ hf
    ((cosliceUniversalPrismLiftEndpoint_identity p b d hd).trans h.symm)

/-- 各 fiber の比較同型は、同じ大域的な相対頂点同型の制限そのもの。 -/
def cosliceUniversalPrismLiftEndpoint_fiberIso
    {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌) (d : E _⦋0⦌)
    (hd : p.app (Opposite.op ⦋0⦌) d = b)
    (f : sliceUnder (SSet.yonedaEquiv.symm b) ⟶ E)
    (hf : f ≫ p = sliceUnderProjection (SSet.yonedaEquiv.symm b))
    (h : f.app (Opposite.op ⦋0⦌) (cosliceIdentityCone b) = d) (r : B _⦋0⦌) :
    FunctorIso
      (vertexFiberMap _ p (cosliceUniversalPrismLiftEndpoint p b d hd)
        (cosliceUniversalPrismLiftEndpoint_projection p b d hd) r)
      (vertexFiberMap _ p f hf r) := by
  have e := VertexIso.map (cosliceUniversalPrismLiftEndpoint_compareIso p b d hd f hf h)
    (relativeFunctorFiberHom (sliceUnderProjection (SSet.yonedaEquiv.symm b)) p r)
  simpa only [relativeFunctorFiberHom_vertex] using e

end SerrePositivity.InfinityCategories
