module

public import SerrePositivity.InfinityCategories.F1.Coherent.RightIntervalCutSimplex
public import SerrePositivity.InfinityCategories.F1.Cocartesian.TransportDiagramHomInterval
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalFunctorHomPrism

/-!
概要：元の全 Hom 作用の prism の値を、切断後の同じ対角評価へ移す。
方針：二重 uncurry を共同実現へ戻し、標準区間比較の切断評価式を使う。
規約：追加パラメーターの全次数と、元の底の射列を保持する。
使われ方：実際の第一三角形の全高次を、固定成分の Hom 計算へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の右 Hom の切断単体を、同じ底の射列上で対角評価する。 -/
def cocartesianTransportHomCutSimplex {C : Type u} [Category.{u} C]
    (F G : CocartesianTransportDiagramCategory C) {n : ℕ}
    (σ : (nerve C) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) : CatInfinity.{u} _⦋n⦌ :=
  cocartesianTransportDiagramDiagonalSimplex σ (coherentRightIntervalCutSimplex s t)

/-- 元の分類作用の実際の prism は、全単体で同じ切断した共同評価に一致する。 -/
lemma cocartesianTransportDiagramHomIntervalPrism_evaluate_cut
    {C : Type u} [Category.{u} C] (F G : CocartesianTransportDiagramCategory C) {n : ℕ}
    (σ : (nerve C) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) :
    (intervalFunctorHomPrism (cocartesianTransportDiagramHomInterval F G)).app
        (Opposite.op ⦋n⦌) ((t, ULift.up σ), ULift.up s) =
      cocartesianTransportHomCutSimplex F G σ s (stdSimplex.objEquiv t).toOrderHom := by
  unfold intervalFunctorHomPrism
  rw [cocartesianTransportDiagramHomInterval_uncurry]
  unfold functorParameterizedPrism
  rw [uncurry_natural_left]
  unfold cocartesianTransportDiagramRealization
  erw [uncurry_natural_left, uncurry_curry]
  change cocartesianTransportDiagramDiagonalSimplex σ
    ((pinchedHomUncurry (coherentHomComparison F G)).app (Opposite.op ⦋n⦌)
      ((rightMappingSpacePrism _).app (Opposite.op ⦋n⦌) (t, ULift.up s))) = _
  rw [rightMappingSpacePrism_evaluate, pinchedHomUncurry_simplex]
  rfl

/-- 時刻零の対角評価の対象は、同じ始域図式の同じ底の値。 -/
lemma cocartesianTransportHomCutSimplex_obj_zero
    {C : Type u} [Category.{u} C] (F G : CocartesianTransportDiagramCategory C) {n : ℕ}
    (σ : (nerve C) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) (hi : t i = 0) :
    (cocartesianTransportHomCutSimplex F G σ s t).obj ⟨ULift.up i⟩ =
      cocartesianTransportDiagramValue F (σ.obj i) :=
  congrArg (fun H ↦ cocartesianTransportDiagramValue H (σ.obj i))
    (coherentRightIntervalCutSimplex_obj_zero s t i hi)

/-- 時刻一の対角評価の対象は、同じ終域図式の同じ底の値。 -/
lemma cocartesianTransportHomCutSimplex_obj_one
    {C : Type u} [Category.{u} C] (F G : CocartesianTransportDiagramCategory C) {n : ℕ}
    (σ : (nerve C) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) (hi : t i = 1) :
    (cocartesianTransportHomCutSimplex F G σ s t).obj ⟨ULift.up i⟩ =
      cocartesianTransportDiagramValue G (σ.obj i) :=
  congrArg (fun H ↦ cocartesianTransportDiagramValue H (σ.obj i))
    (coherentRightIntervalCutSimplex_obj_one s t i hi)

end SerrePositivity.InfinityCategories
