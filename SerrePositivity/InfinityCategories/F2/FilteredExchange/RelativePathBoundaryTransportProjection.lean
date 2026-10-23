module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativePathBoundaryTransportHomotopy

/-!
概要：貼り合わせた全相対境界円柱の両側の制限と、元の模型の底円柱との一致。
方針：押し出しホモトピーの制限式と、元の二つの底射の式を使う。
規約：全円柱を厳密に保持する。
使われ方：標的有限模型の相対 fiber 輸送の底条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K M E D H B : SSet.{u}} {p : H ⟶ B} {f : E ⟶ H} {g : D ⟶ H}
  {A : K.Subcomplex} {u : K ⟶ E} {v : K ⟶ D}
  {a : (A : SSet.{u}) ⟶ fiberwiseIntervalPullback p f g}
  {m : relativePathBoundaryShape A ⟶ M} {q : M ⟶ H}
  (d : RelativePathInputTransportData p f g A u v a m q)
  (hk : (relativePathBoundarySide A ≫ m) ≫ q = fiberwisePullbackPathPrism p f g a)
  (he : (relativePathBoundaryEnds A ≫ m) ≫ q = intervalBoundaryDiagram (u ≫ f) (v ≫ g))

/-- 概要：貼り合わせの部分 path 円柱は元の境界引き戻し射の全 path 正方形。
方針：押し出しホモトピーの第一脚。規約：全正方形。使われ方：指定境界の厳密な保持。 -/
lemma relativePathBoundaryTransportHomotopy_side :
    (relativePathBoundarySide A ▷ (Δ[1] : SSet.{u})) ≫
      (relativePathBoundaryTransportHomotopy d hk he).h =
        (fiberwisePullbackPathPrismHomotopy p f g d.boundaryHomotopy).h :=
  pushoutHomotopy_inl (Subcomplex.unionProd.isPushout (boundary 1) A)
    (relativePathBoundarySideHomotopy d hk) (relativePathBoundaryEndsHomotopy d he)
    (relativePathBoundaryCylinder_compatible d)

/-- 概要：貼り合わせの両端円柱は元の二入力の全境界円柱。
方針：押し出しホモトピーの第二脚。規約：全時間。使われ方：二入力の厳密な保持。 -/
lemma relativePathBoundaryTransportHomotopy_ends :
    (relativePathBoundaryEnds A ▷ (Δ[1] : SSet.{u})) ≫
      (relativePathBoundaryTransportHomotopy d hk he).h = (relativePathEndsHomotopy d).h :=
  pushoutHomotopy_inr (Subcomplex.unionProd.isPushout (boundary 1) A)
    (relativePathBoundarySideHomotopy d hk) (relativePathBoundaryEndsHomotopy d he)
    (relativePathBoundaryCylinder_compatible d)

/-- 概要：全相対境界の輸送円柱の底は、元の有限模型の指定底円柱に厳密に一致。
方針：時間との直積後の押し出しの両脚で底射の式を使う。
規約：全時刻。使われ方：模型本体の境界固定 fiber 輸送。 -/
lemma relativePathBoundaryTransportHomotopy_projection :
    (relativePathBoundaryTransportHomotopy d hk he).h ≫ p =
      (m ▷ (Δ[1] : SSet.{u})) ≫ d.modelBase.h := by
  apply ((Subcomplex.unionProd.isPushout (boundary 1) A).map
    (tensorRight (Δ[1] : SSet.{u}))).hom_ext
  · change (relativePathBoundarySide A ▷ (Δ[1] : SSet.{u})) ≫
      ((relativePathBoundaryTransportHomotopy d hk he).h ≫ p) =
        (relativePathBoundarySide A ▷ (Δ[1] : SSet.{u})) ≫
          ((m ▷ (Δ[1] : SSet.{u})) ≫ d.modelBase.h)
    rw [← Category.assoc, relativePathBoundaryTransportHomotopy_side,
      fiberwisePullbackPathPrismHomotopy_projection, ← comp_whiskerRight_assoc]
    exact d.path_projection.symm
  · change (relativePathBoundaryEnds A ▷ (Δ[1] : SSet.{u})) ≫
      ((relativePathBoundaryTransportHomotopy d hk he).h ≫ p) =
        (relativePathBoundaryEnds A ▷ (Δ[1] : SSet.{u})) ≫
          ((m ▷ (Δ[1] : SSet.{u})) ≫ d.modelBase.h)
    rw [← Category.assoc, relativePathBoundaryTransportHomotopy_ends,
      relativePathEndsHomotopy_projection, ← comp_whiskerRight_assoc]

end SerrePositivity.InfinityCategories.F2
