module
public import SerrePositivity.EInfinity.BarrattEccles.CAlgAlgebraSource
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：strict BE余単体図式と全パラメータ評価を、同じ通常nerveから読む。
方針：元の射列と図式の評価関手を同時評価し、既存algebraCAlgSourceへ後合成。
規約：IS-W2 3b-4 R02の入力の証明分割。図式の厳密化を仮定しない。
使われ方：同じ全Tot錐族の右境界と固定図式の表示。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.SSet _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- 元のstrict BE図式の全nerveを宇宙だけ揃えて読む。 -/
def strictBECosimplicialNerve (F : AsSmall.{u} SimplexCategory ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)) ⟶
      nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra where
  app _ := ↾fun σ => σ.down ⋙ F
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro σ
    rfl

/-- 元のstrict BE図式の同じCAlg図式。 -/
def strictBECosimplicialDiagram (F : AsSmall.{u} SimplexCategory ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)) ⟶ _root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A :=
  _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBECosimplicialNerve A F ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A

/-- 全次数・全図式射を同時に評価する、同じ全通常nerve。 -/
def strictBECosimplicialEvaluationNerve :
    (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)) ⊗
      nerve (AsSmall.{u} SimplexCategory ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) ⟶
        nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra where
  app _ := ↾fun p => (p.1.down.prod' p.2) ⋙
    evaluationUncurried (AsSmall.{u} SimplexCategory) (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro p
    rfl

/-- 同じ全strict BE評価のCAlg像。 -/
def strictBECosimplicialEvaluation :
    (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)) ⊗
      nerve (AsSmall.{u} SimplexCategory ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) ⟶ _root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A :=
  _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBECosimplicialEvaluationNerve A ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A

/-- 固定図式の全評価は元の同じstrict BE図式の全nerveへ戻る。 -/
theorem strictBECosimplicialEvaluationNerve_at
    (F : AsSmall.{u} SimplexCategory ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    inv (fst ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))
      (Δ[0] : SSet.{u+1})) ≫ (𝟙 _ ⊗ₘ SSet.yonedaEquiv.symm (nerveVertex F)) ≫
        _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBECosimplicialEvaluationNerve A = _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBECosimplicialNerve A F := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  let K := (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory))
  let t := (inv (fst K (Δ[0] : SSet.{u+1}))).app n s
  have ht : t.1 = s := by
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (IsIso.inv_hom_id (fst K (Δ[0] : SSet.{u+1}))) n) s
  change (t.1.down.prod' ((SSet.yonedaEquiv.symm (nerveVertex F)).app n t.2)) ⋙
    evaluationUncurried (AsSmall.{u} SimplexCategory) (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra = s.down ⋙ F
  rw [ht]
  apply CategoryTheory.Functor.ext (fun _ => rfl)

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
