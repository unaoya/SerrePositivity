module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModelUnitSixTriangleLoops
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitCapUnitLoopDomains
/-! # 実単位閉路の全円柱写像と元六片の同定

概要：二つの実単位閉路の全時間を、元六片の同じ写像空間三角形の面へ照合する。
方針：関手辺を uncurry し、同じ Hom 模型同型の逆による入力輸送だけを展開する。
規約：正本の両係数対角と元の全入力を保持する。
使われ方：元四面体の二射影面の単位則を実閉路へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "P" => dgGluingNativePinchedHomParameter R C D M X Y

lemma dgGluingModelRightUnitLoop_h :
    (dgGluingModelRightUnitLoop R C D M X Y).h =
      ((dgGluingNativeHomModelIso R C D M X Y).inv ▷ (Δ[1] : SSet.{max (u + 1) v w})) ≫
        (β_ P (Δ[1] : SSet.{max (u + 1) v w})).hom ≫
          (stdSimplex.δ (0 : Fin 3) ▷ P) ≫
            dgGluingNativeUnitCapIntervalTriangle R C D M X Y 0 := by
  change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv
    (stdSimplex.δ (0 : Fin 3) ≫ dgGluingModelUnitCapTriangleDiagram R C D M X Y 0))) = _
  rw [Equiv.symm_apply_apply, dgGluingModelUnitCapTriangleDiagram,
    dgGluingTriangleDiagramTransport_face, uncurry_curry]

lemma dgGluingModelLeftUnitLoop_h :
    (dgGluingModelLeftUnitLoop R C D M X Y).h =
      ((dgGluingNativeHomModelIso R C D M X Y).inv ▷ (Δ[1] : SSet.{max (u + 1) v w})) ≫
        (β_ P (Δ[1] : SSet.{max (u + 1) v w})).hom ≫
          (stdSimplex.δ (2 : Fin 3) ▷ P) ≫
            dgGluingNativeUnitCapIntervalTriangle R C D M X Y 2 := by
  change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv
    (stdSimplex.δ (2 : Fin 3) ≫ dgGluingModelUnitCapTriangleDiagram R C D M X Y 2))) = _
  rw [Equiv.symm_apply_apply, dgGluingModelUnitCapTriangleDiagram,
    dgGluingTriangleDiagramTransport_face, uncurry_curry]
end SerrePositivity.InfinityCategories
