module

public import SerrePositivity.InfinityCategories.F2.Presentable.ConstantEvaluationHomTransport
public import SerrePositivity.InfinityCategories.F2.Presentable.ConeFunctorCounitPrism

/-!
概要：定値始域から全錐への射を、頂点評価と錐の余単位で因子化する。
方針：前合成作用の自然性を、同じ端点の等式による輸送で照合する。
規約：元の射の類と全ホモトピーを保持する。
使われ方：極限錐の余単位による Hom 全単射の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open SSet.Truncated.HomotopyCategory

/-- 概要：定値始域からの射の頂点評価の定値化は、定値前合成に一致する。
方針：評価と定値化の比較に始点の等式の同型を補う。
規約：元の指定 Hom の類を使う。
使われ方：錐の余単位の Hom 公式の端点正規化。 -/
lemma constantSourceEvaluationHom_transport {A B X : SSet.{u}} (H : B ⟶ X)
    (x : B _⦋0⦌) (y : X _⦋0⦌) (α : FunctorHom (SSet.const y) H) :
    constantFunctorHomMap A
      (eqToHom (congrArg HomotopyCategory.mk (ssetConst_zero_apply y x)).symm ≫
        functorHomEvaluate α x) =
    F1B.kanFunctorHomCongr (SSet.comp_const (SSet.const x : A ⟶ B) y)
      (SSet.const_comp x H)
      ((hoFunctor.map ((pre (SSet.const x : A ⟶ B)).app X)).toFunctor.map α) := by
  rw [constantFunctorHomMap_comp, ← functorHomEvaluate_constantFunctorHomMap A α x]
  simp only [constantFunctorCompIso, F1B.kanFunctorHomCongr, Iso.homCongr_apply,
    eqToIso.inv, eqToIso.hom, constantFunctorHomMap, eqToHom_map,
    eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

/-- 概要：定値始域からの射の後端制限は前端制限と形状ホモトピーで因子化する。
方針：前合成作用の自然性で、定値始域での成分を恒等射へ簡約する。
規約：形状ホモトピーの可逆性を要求しない。
使われ方：元の錐の余単位の普遍性。 -/
lemma precompositionHomotopy_constant_source_naturality {A B X : SSet.{u}}
    {f g : A ⟶ B} (T : SSet.Homotopy f g) (H : B ⟶ X) (y : X _⦋0⦌)
    (α : FunctorHom (SSet.const y) H) :
    (hoFunctor.map ((pre g).app X)).toFunctor.map α =
      (hoFunctor.map ((pre f).app X)).toFunctor.map α ≫
        homMk (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp T H)) := by
  have hn := (F1B.precompositionNatTrans T X).naturality α
  erw [F1B.precompositionNatTrans_app, F1B.precompositionNatTrans_app] at hn
  have hc := F1B.homotopyHom_eqToHom
    (functorHomotopyPostcomp T (SSet.const y))
    (by simp only [SSet.comp_const]) (by simp only [functorHomotopyPostcomp, SSet.comp_const])
  rw [hc] at hn
  simp only [SSet.comp_const] at hn
  exact (Category.id_comp _).symm.trans hn.symm

/-- 概要：形状ホモトピーの余単位と頂点評価の定値化は底の制限を与える。
方針：始端・中間・終端を同じ等式で輸送し、全前合成の自然性を使う。
規約：指定した元の射そのものを比較する。
使われ方：普遍錐の余単位による Hom 全単射。 -/
lemma constantEndpointCounitHom_evaluation {A B X : SSet.{u}}
    {g : A ⟶ B} (x : B _⦋0⦌) (T : SSet.Homotopy (SSet.const x) g)
    (H : B ⟶ X) {p : A ⟶ X} (hp : g ≫ H = p)
    (y : X _⦋0⦌) (α : FunctorHom (SSet.const y) H) :
    constantFunctorHomMap A
      (eqToHom (congrArg HomotopyCategory.mk (ssetConst_zero_apply y x)).symm ≫
        functorHomEvaluate α x) ≫
      F1B.kanFunctorHomCongr (SSet.const_comp x H) hp
        (homMk (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp T H))) =
    F1B.kanFunctorHomCongr (SSet.comp_const g y) hp
      ((hoFunctor.map ((pre g).app X)).toFunctor.map α) := by
  rw [constantSourceEvaluationHom_transport]
  exact (functorHomCongr_comp (SSet.comp_const (SSet.const x) y)
    (SSet.const_comp x H) hp _ _).symm.trans
    (congrArg (F1B.kanFunctorHomCongr (SSet.comp_const g y) hp)
      (precompositionHomotopy_constant_source_naturality T H y α).symm)

end SerrePositivity.InfinityCategories.F2.Presentable
