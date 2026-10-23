module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TransportMixedHomNaturality
public import SerrePositivity.InfinityCategories.F1.Coherent.HomReindex

/-!
概要：実際の source の成分 fiber における coherent 比較の混合 Hom を計算する。
方針：同じ fiber 上の混合作用の等式を Yoneda 族へ制限し、最大元の path 評価へ移す。
規約：宇宙を持ち上げた元の source の任意の次数の単体を使う。
使われ方：元の第一三角形全体と指定合成三角形の高次 Hom 作用の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] {c d : C} (f : c ⟶ d)
  (F G : CocartesianTransportDiagramCategory C)

/-- 同じ成分 fiber の単体の Yoneda 族で、元の混合作用は指定頂点に定値。 -/
lemma cocartesianTransportMixedHom_fiber_yoneda
    (b : (SimplicialCategory.sHom (cocartesianTransportDiagramValue F d)
      (cocartesianTransportDiagramValue G d)) _⦋0⦌) {n : ℕ}
    (s : (vertexFiber ((cocartesianTransportDiagramEvaluationEnriched d).map F G) b) _⦋n⦌) :
    SSet.yonedaEquiv.symm s.val ≫ cocartesianTransportDiagramMixedHom f F G =
      SSet.const ((quasicategoryCoreMap ((pre (F.val.map f)).app (G.val.obj d))).app
        (Opposite.op ⦋0⦌) b) := by
  have h := congrArg (fun q ↦ SSet.yonedaEquiv.symm s ≫ q)
    (cocartesianTransportDiagramMixedHom_fiber f F G b)
  rw [← Category.assoc, SSet.yonedaEquiv_symm_comp, SSet.comp_const] at h
  exact h

/-- 同じ元の source 比較の単体を宇宙から戻しても、混合 Yoneda 族は同じ頂点に定値。 -/
lemma cocartesianHomSourceComponent_mixedHom_yoneda
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (cocartesianTransportDiagramValue F d)
        (cocartesianTransportDiagramValue G d))) _⦋0⦌) {n : ℕ}
    (s : (vertexFiber (cocartesianHomSourceComponent F G d) b) _⦋n⦌) :
    SSet.yonedaEquiv.symm s.val.down ≫ cocartesianTransportDiagramMixedHom f F G =
      SSet.const ((quasicategoryCoreMap ((pre (F.val.map f)).app (G.val.obj d))).app
        (Opposite.op ⦋0⦌) b.down) := by
  let s' : (vertexFiber ((cocartesianTransportDiagramEvaluationEnriched d).map F G)
      b.down) _⦋n⦌ := ⟨s.val.down, congrArg ULift.down s.property⟩
  exact cocartesianTransportMixedHom_fiber_yoneda f F G b.down s'

/-- 元の coherent Hom 比較の最後に向かう全 path 作用も、同じ混合頂点に定値。 -/
lemma cocartesianHomSourceComponent_coherentMixedHom
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (cocartesianTransportDiagramValue F d)
        (cocartesianTransportDiagramValue G d))) _⦋0⦌) {n : ℕ}
    (s : (vertexFiber (cocartesianHomSourceComponent F G d) b) _⦋n⦌) (i : Fin (n + 1)) :
    (coherentHomComparisonHom s.val.down i.castSucc (Fin.last (n + 1)) ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          (coherentHomComparisonObj_cast F G i) (coherentHomComparisonObj_last F G n))) ≫
        cocartesianTransportDiagramMixedHom f F G =
      SSet.const ((quasicategoryCoreMap ((pre (F.val.map f)).app (G.val.obj d))).app
        (Opposite.op ⦋0⦌) b.down) := by
  rw [coherentHomComparisonHom_cast_last, Category.assoc,
    cocartesianHomSourceComponent_mixedHom_yoneda f F G b s, SSet.comp_const]

end SerrePositivity.InfinityCategories
