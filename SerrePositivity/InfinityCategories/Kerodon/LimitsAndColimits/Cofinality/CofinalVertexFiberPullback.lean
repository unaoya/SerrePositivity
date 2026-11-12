module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.TerminalFiberCofinality

/-!
概要：直接定義した頂点 fiber と通常の pullback の同型。
方針：元の全空間への包含と一点への唯一の射を引き戻しへ持ち上げる。
規約：fibration 性や quasicategory 性は不要。
使われ方：終点 fiber の包含の定理を標準の pullback 射影へ移す。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：頂点 fiber はその頂点包含への pullback と厳密に同型。
方針：第一射影を両方向の射の元の全空間への作用とし、第二射影は一点への一意性で処理する。
規約：一点は Δ[0]、頂点包含は Yoneda の逆対応。
使われ方：cofinality の pullback の射の計算。 -/
noncomputable def cofinalVertexFiberPullbackIso {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ≅ pullback p (SSet.yonedaEquiv.symm b) where
  hom := pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b)
    (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.yonedaEquiv_symm_zero, SSet.comp_const])
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b (pullback.fst p (SSet.yonedaEquiv.symm b)) (by
    rw [pullback.condition, SSet.yonedaEquiv_symm_zero, SSet.comp_const])
  hom_inv_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, pullback.lift_fst, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, Category.id_comp]
    · exact stdSimplex.isTerminalObj₀.hom_ext _ _

/-- 概要：頂点 fiber の同型は元の全空間への包含を保つ。
方針：pullback への持ち上げの第一射影の式。
規約：標準の第一射影との厳密な等式。
使われ方：anodyne 性の同型による移送。 -/
lemma cofinalVertexFiberPullbackIso_hom_fst {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (cofinalVertexFiberPullbackIso p b).hom ≫ pullback.fst p (SSet.yonedaEquiv.symm b) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b :=
  pullback.lift_fst _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
