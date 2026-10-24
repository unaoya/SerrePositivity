module
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomEvaluation
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomEvaluationNaturality
/-!
概要：全関手射の定値制限を同じ頂点成分の定値族として比較する。
方針：既存の全評価公式から等式による端点輸送を Arrow 圏に回収する。
規約：全パラメータと元の射を保持する。
使われ方：実忘却の全源同型の定値制限と元の頂点同型の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory SSet MonoidalClosed SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：全関手同型の同じ二射を頂点で評価した実頂点同型。
方針：元の全逆則を同じ評価の恒等・合成則へ送る。
規約：元の二射を保持。使われ方：定値制限の全族公式に一致する端点同型。 -/
def functorIsoEvaluate {L X : SSet.{u}} {F G : L ⟶ X} (e : FunctorIso F G)
    (x : L.obj (Opposite.op ⦋0⦌)) :
    VertexIso (F.app (Opposite.op ⦋0⦌) x) (G.app (Opposite.op ⦋0⦌) x) where
  hom := functorHomEvaluate e.hom x
  inv := functorHomEvaluate e.inv x
  hom_inv_id := by
    rw [← functorHomEvaluate_comp, e.hom_inv_id, functorHomEvaluate_id]
  inv_hom_id := by
    rw [← functorHomEvaluate_comp, e.inv_hom_id, functorHomEvaluate_id]

/-- 概要：同じ二射の評価は既存の全関手同型の頂点成分そのもの。
方針：既存の自然変換成分と評価の一致を同型の順射へ適用する。
規約：既存の頂点比較を変更しない。使われ方：標準単位の既存端点比較との接続。 -/
lemma functorIsoEvaluate_eq_app {L X : SSet.{u}} [Quasicategory L] [Quasicategory X]
    {F G : L ⟶ X} (e : FunctorIso F G) (x : L.obj (Opposite.op ⦋0⦌)) :
    functorIsoEvaluate e x = e.app x := by
  apply Iso.ext
  change functorHomEvaluate e.hom x = (functorCellToNatTrans e.hom).app (HomotopyCategory.mk x)
  exact (functorCellToNatTrans_app_eq_evaluate e.hom x).symm

/-- 概要：同じ頂点同型の二射を全パラメータの定値関手同型へ送る。
方針：既存の定値射の恒等・合成則へ元の逆則を送る。
規約：元の二射を保持。使われ方：全源比較の両端の逆を含む全族輸送。 -/
def constantVertexIso (K : SSet.{u}) {X : SSet.{u}}
    {x y : X.obj (Opposite.op ⦋0⦌)} (e : VertexIso x y) :
    FunctorIso (SSet.const x : K ⟶ X) (SSet.const y : K ⟶ X) where
  hom := constantFunctorHomMap K e.hom
  inv := constantFunctorHomMap K e.inv
  hom_inv_id := by
    rw [← constantFunctorHomMap_comp, e.hom_inv_id, constantFunctorHomMap_id]
  inv_hom_id := by
    rw [← constantFunctorHomMap_comp, e.inv_hom_id, constantFunctorHomMap_id]

/-- 概要：全関手射の定値制限は同じ頂点成分の定値族と全 Arrow として一致する。
方針：元の全評価等式の両端の等式輸送を記録する。
規約：任意のパラメータ K。使われ方：全源同型の定値制限の照合。 -/
lemma constantRestriction_arrow (K : SSet.{u}) {L X : SSet.{u}} {F G : L ⟶ X}
    (a : FunctorHom F G) (x : L.obj (Opposite.op ⦋0⦌)) :
    Arrow.mk ((hoFunctor.map ((pre (SSet.const x : K ⟶ L)).app X)).toFunctor.map a) =
      Arrow.mk (constantFunctorHomMap K (functorHomEvaluate a x)) := by
  apply (Arrow.mk_eq_mk_iff _ _).mpr
  refine ⟨congrArg (fun f => HomotopyCategory.mk (functorVertex f)) (SSet.const_comp x F),
    congrArg (fun f => HomotopyCategory.mk (functorVertex f)) (SSet.const_comp x G), ?_⟩
  rw [← functorHomEvaluate_constantFunctorHomMap K a x]
  simp [constantFunctorCompIso, Category.assoc]

/-- 概要：頂点の等式で輸送した同じ射の定値族は元の定値族と全 Arrow として一致する。
方針：元の頂点等式を消去する。
規約：元の射と全パラメータを保持。使われ方：通常忘却の頂点表示の輸送。 -/
lemma constantHom_transport_arrow (K : SSet.{u}) {X : SSet.{u}}
    {x y x' y' : X.obj (Opposite.op ⦋0⦌)} (hx : x = x') (hy : y = y')
    (f : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y) :
    Arrow.mk (constantFunctorHomMap K
      (eqToHom (congrArg HomotopyCategory.mk hx).symm ≫ f ≫
        eqToHom (congrArg HomotopyCategory.mk hy))) =
      Arrow.mk (constantFunctorHomMap K f) := by
  cases hx
  cases hy
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end SerrePositivity.EInfinity.FrameHom
