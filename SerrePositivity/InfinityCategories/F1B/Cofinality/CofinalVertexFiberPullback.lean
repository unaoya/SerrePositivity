module

public import SerrePositivity.InfinityCategories.F1B.Cofinality.TerminalFiberCofinality

/-!
概要：直接定義した頂点 fiber と通常の pullback の同型。
方針：元の全空間への包含と一点への唯一の射を引き戻しへ持ち上げる。
規約：fibration 性や quasicategory 性は不要。
使われ方：終点 fiber の包含の定理を標準の pullback 射影へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：頂点 fiber はその頂点包含への pullback と厳密に同型。
方針：第一射影を両方向の射の元の全空間への作用とし、第二射影は一点への一意性で処理する。
規約：一点は Δ[0]、頂点包含は Yoneda の逆対応。
使われ方：cofinality の pullback の射の計算。 -/
noncomputable def cofinalVertexFiberPullbackIso {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    vertexFiber p b ≅ pullback p (SSet.yonedaEquiv.symm b) where
  hom := pullback.lift (vertexFiberι p b)
    (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (by
      rw [vertexFiberι_comp, SSet.yonedaEquiv_symm_zero, SSet.comp_const])
  inv := vertexFiberLift p b (pullback.fst p (SSet.yonedaEquiv.symm b)) (by
    rw [pullback.condition, SSet.yonedaEquiv_symm_zero, SSet.comp_const])
  hom_inv_id := by
    apply vertexFiber_hom_ext p b
    rw [Category.assoc, vertexFiberLift_ι, pullback.lift_fst, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, vertexFiberLift_ι, Category.id_comp]
    · exact stdSimplex.isTerminalObj₀.hom_ext _ _

/-- 概要：頂点 fiber の同型は元の全空間への包含を保つ。
方針：pullback への持ち上げの第一射影の式。
規約：標準の第一射影との厳密な等式。
使われ方：anodyne 性の同型による移送。 -/
lemma cofinalVertexFiberPullbackIso_hom_fst {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (cofinalVertexFiberPullbackIso p b).hom ≫ pullback.fst p (SSet.yonedaEquiv.symm b) =
      vertexFiberι p b :=
  pullback.lift_fst _ _ _

end SerrePositivity.InfinityCategories
