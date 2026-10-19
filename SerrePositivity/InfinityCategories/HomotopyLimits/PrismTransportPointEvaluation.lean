module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PrismCylinderParameter
public import SerrePositivity.InfinityCategories.HomotopyLimits.PrismVertexEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.PrismTransportIdentity
public import SerrePositivity.InfinityCategories.HomotopyLimits.FunctorIsoPointEvaluation

/-!
概要：全パラメータの prism 輸送同型の成分を、同じ prism の一点制限と照合する。
方針：係数変更で保たれる輸送同型の射を、一点の関手空間の評価へ写す。
規約：始域の Kan 性や比較円柱の選び直しは不要。使われ方：三角形の端辺の成分計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
/-- 一点への係数変更は、同じ頂点評価を第一射影から引き戻したもの。 -/
lemma prismParameterPrecomp_point {A E : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) (x : A _⦋0⦌) :
    prismParameterPrecomp H (SSet.yonedaEquiv.symm x) =
      fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) ≫ prismVertexEvaluation H x := by
  rw [prismParameterPrecomp, prismVertexEvaluation, SSet.yonedaEquiv_symm_zero]
  rw [← Category.assoc, comp_lift, Category.comp_id, SSet.comp_const]
  rfl

variable {A E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  {a b : B _⦋0⦌} (e : B.Edge a b) (f : A ⟶ vertexFiber p a)

/-- 全族の輸送比較の成分は、同じ入力 prism を一点へ制限した比較の評価である。 -/
lemma prismTransportComponent_hom_arrow (g : A ⟶ vertexFiber p b)
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (hH₀ : prismEndpoint 0 A ≫ H = f ≫ vertexFiberι p a)
    (hH₁ : prismEndpoint 1 A ≫ H = g ≫ vertexFiberι p b)
    (hHp : H ≫ p = fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge)
    (x : A _⦋0⦌) :
    Arrow.mk ((leftFibrationPrism_transportIso p e f g H hH₀ hH₁ hHp).toNatIso.hom.app
      (SSet.HomotopyCategory.mk x)) =
      Arrow.mk (VertexIso.map
        (leftFibrationPrism_transportIso p e (SSet.yonedaEquiv.symm x ≫ f)
          (SSet.yonedaEquiv.symm x ≫ g) (prismParameterPrecomp H (SSet.yonedaEquiv.symm x))
          (prismParameterPrecomp_zero p f H hH₀ (SSet.yonedaEquiv.symm x))
          (prismParameterPrecomp_one p H (SSet.yonedaEquiv.symm x) g hH₁)
          (prismParameterPrecomp_projection p e H hHp (SSet.yonedaEquiv.symm x)))
        (pointFunctorEvaluationIso (vertexFiber p b)).hom).hom := by
  refine (functorIsoComponent_point_hom_arrow
    (leftFibrationPrism_transportIso p e f g H hH₀ hH₁ hHp) x).trans ?_
  exact congrArg
    (hoFunctor.map (pointFunctorEvaluationIso (vertexFiber p b)).hom).toFunctor.mapArrow.obj
    (prismTransportIso_parameter_hom_arrow p e f H hH₀ hHp
      (SSet.yonedaEquiv.symm x) g hH₁).symm

/-- 同じ raw な prism の輸送比較は、初期値・終点の表示を変えても同じ射を表す。 -/
lemma prismTransportIso_raw_hom_arrow (g : A ⟶ vertexFiber p b)
    (H H' : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (hH₀ : prismEndpoint 0 A ≫ H = f ≫ vertexFiberι p a)
    (hH₁ : prismEndpoint 1 A ≫ H = g ≫ vertexFiberι p b)
    (hHp : H ≫ p = fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge)
    (f' : A ⟶ vertexFiber p a) (g' : A ⟶ vertexFiber p b)
    (hH₀' : prismEndpoint 0 A ≫ H' = f' ≫ vertexFiberι p a)
    (hH₁' : prismEndpoint 1 A ≫ H' = g' ≫ vertexFiberι p b)
    (hHp' : H' ≫ p = fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge)
    (h : H = H') :
    Arrow.mk (leftFibrationPrism_transportIso p e f g H hH₀ hH₁ hHp).hom =
      Arrow.mk (leftFibrationPrism_transportIso p e f' g' H' hH₀' hH₁' hHp').hom := by
  subst H'
  have hf : f = f' := vertexFiber_hom_ext p a (hH₀.symm.trans hH₀')
  have hg : g = g' := vertexFiber_hom_ext p b (hH₁.symm.trans hH₁')
  subst f' g'
  rfl

/-- 一点で同じ標準 prism になる全族の比較成分は、標準終点の恒等射である。 -/
lemma prismTransportComponent_standard_hom_arrow (g : A ⟶ vertexFiber p b)
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (hH₀ : prismEndpoint 0 A ≫ H = f ≫ vertexFiberι p a)
    (hH₁ : prismEndpoint 1 A ≫ H = g ≫ vertexFiberι p b)
    (hHp : H ≫ p = fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge)
    (x : A _⦋0⦌) (f₀ : (Δ[0] : SSet.{u}) ⟶ vertexFiber p a)
    (hx : prismParameterPrecomp H (SSet.yonedaEquiv.symm x) =
      prismTransportStandard p e f₀) :
    Arrow.mk ((leftFibrationPrism_transportIso p e f g H hH₀ hH₁ hHp).toNatIso.hom.app
      (SSet.HomotopyCategory.mk x)) =
      Arrow.mk (𝟙 (SSet.HomotopyCategory.mk
        ((pointFunctorEvaluationIso (vertexFiber p b)).hom.app _
          (functorVertex (f₀ ≫ edgeTransport p e))))) := by
  refine (prismTransportComponent_hom_arrow p e f g H hH₀ hH₁ hHp x).trans ?_
  have hc := prismTransportIso_raw_hom_arrow p e
    (SSet.yonedaEquiv.symm x ≫ f) (SSet.yonedaEquiv.symm x ≫ g)
    (prismParameterPrecomp H (SSet.yonedaEquiv.symm x)) (prismTransportStandard p e f₀)
    (prismParameterPrecomp_zero p f H hH₀ (SSet.yonedaEquiv.symm x))
    (prismParameterPrecomp_one p H (SSet.yonedaEquiv.symm x) g hH₁)
    (prismParameterPrecomp_projection p e H hHp (SSet.yonedaEquiv.symm x))
    f₀ (f₀ ≫ edgeTransport p e)
    (prismTransportStandard_zero p e f₀) (prismTransportStandard_one p e f₀)
    (prismTransportStandard_projection p e f₀) hx
  have hm := congrArg
    (hoFunctor.map (pointFunctorEvaluationIso (vertexFiber p b)).hom).toFunctor.mapArrow.obj hc
  refine hm.trans ?_
  change Arrow.mk ((hoFunctor.map (pointFunctorEvaluationIso (vertexFiber p b)).hom).toFunctor.map
    (leftFibrationPrism_transportIso p e f₀ (f₀ ≫ edgeTransport p e)
      (prismTransportStandard p e f₀) (prismTransportStandard_zero p e f₀)
      (prismTransportStandard_one p e f₀) (prismTransportStandard_projection p e f₀)).hom) = _
  rw [prismTransportIso_standard_hom, CategoryTheory.Functor.map_id]
  rfl

end
end SerrePositivity.InfinityCategories.HomotopyLimits
