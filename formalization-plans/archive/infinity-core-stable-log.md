# α-S の公開宣言の型一覧

## S1：零対象・余極限・押し出し・fiber/cofiber

```lean
@SerrePositivity.InfinityCategories.JoinCocone.{u_1} : {K X : SSet.{u_1}} → Quiver.Hom.{u_1, u_1 + 1} K X → Type u_1
@SerrePositivity.InfinityCategories.JoinCocone.vertex.{u_1} : {K X : SSet.{u_1}} →
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} →
    SerrePositivity.InfinityCategories.JoinCocone.{u_1} p →
      CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })
@SerrePositivity.InfinityCategories.JoinCocone.vertex_eq.{u_1} : ∀ {K X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p),
  Eq.{u_1 + 1} (SerrePositivity.InfinityCategories.JoinCocone.vertex.{u_1} c)
    (SSet.yonedaEquiv.{u_1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.joinInr.{u_1} K
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
        ↑c))
@SerrePositivity.InfinityCategories.IsColimitCone.{u_1} : {K X : SSet.{u_1}} →
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} → SerrePositivity.InfinityCategories.JoinCocone.{u_1} p → Prop
@SerrePositivity.InfinityCategories.HasColimit.{u_1} : {K X : SSet.{u_1}} → Quiver.Hom.{u_1, u_1 + 1} K X → Prop
@SerrePositivity.InfinityCategories.isColimitCone_iff_trivialKanFibration.{u_1} : ∀ {K X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p),
  SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c ↔
    SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1}
      (SerrePositivity.InfinityCategories.sliceUnderProjection.{u_1}
        ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1}) c))
@SerrePositivity.InfinityCategories.colimitConeIso.{u_1} : {K X : SSet.{u_1}} →
  [SSet.Quasicategory.{u_1} X] →
    {p : Quiver.Hom.{u_1, u_1 + 1} K X} →
      (c d : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p) →
        SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c →
          SerrePositivity.InfinityCategories.IsColimitCone.{u_1} d →
            CategoryTheory.Iso.{u_1, u_1} (SSet.HomotopyCategory.mk.{u_1} c) (SSet.HomotopyCategory.mk.{u_1} d)
@SerrePositivity.InfinityCategories.colimitVertexIso.{u_1} : {K X : SSet.{u_1}} →
  [SSet.Quasicategory.{u_1} X] →
    {p : Quiver.Hom.{u_1, u_1 + 1} K X} →
      (c d : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p) →
        SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c →
          SerrePositivity.InfinityCategories.IsColimitCone.{u_1} d →
            CategoryTheory.Iso.{u_1, u_1}
              (SSet.HomotopyCategory.mk.{u_1} (SerrePositivity.InfinityCategories.JoinCocone.vertex.{u_1} c))
              (SSet.HomotopyCategory.mk.{u_1} (SerrePositivity.InfinityCategories.JoinCocone.vertex.{u_1} d))
@SerrePositivity.InfinityCategories.joinCoconeFamilyEquiv.{u_1} : {A K X : SSet.{u_1}} →
  (p : Quiver.Hom.{u_1, u_1 + 1} K X) →
    Equiv.{u_1 + 1, u_1 + 1} (Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.sliceUnder.{u_1} p))
      (Subtype.{u_1 + 1} fun F =>
        Eq.{u_1 + 1}
          (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.joinInl.{u_1} K A) F)
          p)
SerrePositivity.InfinityCategories.spanCoconeTriangleLeft.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
  (SerrePositivity.InfinityCategories.join.{u_1} (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 0))
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
SerrePositivity.InfinityCategories.spanCoconeTriangleRight.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
  (SerrePositivity.InfinityCategories.join.{u_1} (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 0))
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
SerrePositivity.InfinityCategories.spanCocone_gluing.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (CategoryTheory.Iso.inv.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.joinStdSimplexIso.{u_1} 0 0))
    (SerrePositivity.InfinityCategories.joinMap.{u_1}
      (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} 1)
      (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))))
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} 1)
    (CategoryTheory.Iso.inv.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.joinStdSimplexIso.{u_1} 1 0)))
SerrePositivity.InfinityCategories.spanCocone_isPushout.{u_1} : CategoryTheory.IsPushout.{u_1, u_1 + 1}
  (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} 1)
  (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} 1)
  SerrePositivity.InfinityCategories.spanCoconeTriangleLeft.{u_1}
  SerrePositivity.InfinityCategories.spanCoconeTriangleRight.{u_1}
SerrePositivity.InfinityCategories.spanCoconeSquareIso.{u_1} : CategoryTheory.Iso.{u_1, u_1 + 1}
  (SerrePositivity.InfinityCategories.join.{u_1} (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 0))
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
  (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
SerrePositivity.InfinityCategories.spanCoconeSquareIso_left.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.spanCoconeTriangleLeft.{u_1}
    (CategoryTheory.Iso.hom.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.spanCoconeSquareIso.{u_1}))
  (SerrePositivity.InfinityCategories.squareTriangle.{u_1} 1)
SerrePositivity.InfinityCategories.spanCoconeSquareIso_right.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.spanCoconeTriangleRight.{u_1}
    (CategoryTheory.Iso.hom.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.spanCoconeSquareIso.{u_1}))
  (SerrePositivity.InfinityCategories.squareTriangle.{u_1} 0)
SerrePositivity.InfinityCategories.squareBottomEdge.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
  (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
SerrePositivity.InfinityCategories.squareLeftEdge.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
  (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
SerrePositivity.InfinityCategories.spanSquareBoundary.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 0))
  (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
@SerrePositivity.InfinityCategories.pushoutSpan.{u_1} : {X : SSet.{u_1}} →
  Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X →
    Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 0)) X
@SerrePositivity.InfinityCategories.pushoutCocone.{u_1} : {X : SSet.{u_1}} →
  (F :
      Quiver.Hom.{u_1, u_1 + 1}
        (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
        X) →
    SerrePositivity.InfinityCategories.JoinCocone.{u_1} (SerrePositivity.InfinityCategories.pushoutSpan.{u_1} F)
@SerrePositivity.InfinityCategories.IsPushoutSquare.{u_1} : {X : SSet.{u_1}} →
  Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X →
    Prop
SerrePositivity.InfinityCategories.joinStdSimplexIso_one_zero_inl.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (SerrePositivity.InfinityCategories.joinInl.{u_1}
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
    (CategoryTheory.Iso.hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.joinStdSimplexIso.{u_1} 1 0)))
  (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} 2)
SerrePositivity.InfinityCategories.spanSquareBoundary_bottomEdge.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SSet.horn₂₀.ι₀₁.{u_1}
    SerrePositivity.InfinityCategories.spanSquareBoundary.{u_1})
  SerrePositivity.InfinityCategories.squareBottomEdge.{u_1}
SerrePositivity.InfinityCategories.spanSquareBoundary_leftEdge.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SSet.horn₂₀.ι₀₂.{u_1}
    SerrePositivity.InfinityCategories.spanSquareBoundary.{u_1})
  SerrePositivity.InfinityCategories.squareLeftEdge.{u_1}
@SerrePositivity.InfinityCategories.isPushoutSquare_iff_trivialKanFibration.{u_1} : ∀ {X : SSet.{u_1}}
  (F :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X),
  SerrePositivity.InfinityCategories.IsPushoutSquare.{u_1} F ↔
    SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1}
      (SerrePositivity.InfinityCategories.sliceUnderProjection.{u_1}
        ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1})
          (SerrePositivity.InfinityCategories.pushoutCocone.{u_1} F)))
@SerrePositivity.InfinityCategories.IsZeroVertex.{u_1} : {X : SSet.{u_1}} →
  CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 }) → Prop
SerrePositivity.InfinityCategories.ZeroVertex.{u_1} : SSet.{u_1} → Type u_1
@SerrePositivity.InfinityCategories.ZeroVertex.mk.{u_1} : {X : SSet.{u_1}} →
  (vertex : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })) →
    SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} vertex →
      SerrePositivity.InfinityCategories.IsTerminalVertex.{u_1} vertex →
        SerrePositivity.InfinityCategories.ZeroVertex.{u_1} X
SerrePositivity.InfinityCategories.HasZeroVertex.{u_1} : SSet.{u_1} → Prop
@SerrePositivity.InfinityCategories.HasZeroVertex.mk.{u_1} : ∀ {X : SSet.{u_1}},
  (∃ z, SerrePositivity.InfinityCategories.IsZeroVertex.{u_1} z) →
    SerrePositivity.InfinityCategories.HasZeroVertex.{u_1} X
@SerrePositivity.InfinityCategories.ZeroVertex.isZero.{u_1} : ∀ {X : SSet.{u_1}}
  (z : SerrePositivity.InfinityCategories.ZeroVertex.{u_1} X),
  SerrePositivity.InfinityCategories.IsZeroVertex.{u_1} (SerrePositivity.InfinityCategories.ZeroVertex.vertex.{u_1} z)
SerrePositivity.InfinityCategories.chosenZeroVertex.{u_1} : (X : SSet.{u_1}) →
  [SerrePositivity.InfinityCategories.HasZeroVertex.{u_1} X] → SerrePositivity.InfinityCategories.ZeroVertex.{u_1} X
@SerrePositivity.InfinityCategories.zeroVertexIso.{u_1} : {X : SSet.{u_1}} →
  [SSet.Quasicategory.{u_1} X] →
    (z w : SerrePositivity.InfinityCategories.ZeroVertex.{u_1} X) →
      CategoryTheory.Iso.{u_1, u_1}
        (SSet.HomotopyCategory.mk.{u_1} (SerrePositivity.InfinityCategories.ZeroVertex.vertex.{u_1} z))
        (SSet.HomotopyCategory.mk.{u_1} (SerrePositivity.InfinityCategories.ZeroVertex.vertex.{u_1} w))
@SerrePositivity.InfinityCategories.squareVertex.{u_1} : {X : SSet.{u_1}} →
  Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X →
    Fin 2 → Fin 2 → CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })
SerrePositivity.InfinityCategories.ZeroTriangle.{u_1} : SSet.{u_1} → Type u_1
@SerrePositivity.InfinityCategories.ZeroTriangle.mk.{u_1} : {X : SSet.{u_1}} →
  (square :
      Quiver.Hom.{u_1, u_1 + 1}
        (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
        X) →
    SerrePositivity.InfinityCategories.IsZeroVertex.{u_1}
        (SerrePositivity.InfinityCategories.squareVertex.{u_1} square 0 1) →
      SerrePositivity.InfinityCategories.ZeroTriangle.{u_1} X
@SerrePositivity.InfinityCategories.IsFiberSequence.{u_1} : {X : SSet.{u_1}} →
  SerrePositivity.InfinityCategories.ZeroTriangle.{u_1} X → Prop
@SerrePositivity.InfinityCategories.IsCofiberSequence.{u_1} : {X : SSet.{u_1}} →
  SerrePositivity.InfinityCategories.ZeroTriangle.{u_1} X → Prop
@SerrePositivity.InfinityCategories.FiberSquare.{u_1} : {X : SSet.{u_1}} →
  {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} →
    SSet.Truncated.Edge.{u_1} x y → Type u_1
@SerrePositivity.InfinityCategories.FiberSquare.mk.{u_1} : {X : SSet.{u_1}} →
  {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} →
    {f : SSet.Truncated.Edge.{u_1} x y} →
      (toZeroTriangle : SerrePositivity.InfinityCategories.ZeroTriangle.{u_1} X) →
        Eq.{u_1 + 1}
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.squareRightEdge.{u_1}
              (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u_1} toZeroTriangle))
            ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1}) (SSet.Truncated.Edge.edge.{u_1} f)) →
          SerrePositivity.InfinityCategories.IsPullbackSquare.{u_1}
              (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u_1} toZeroTriangle) →
            SerrePositivity.InfinityCategories.FiberSquare.{u_1} f
@SerrePositivity.InfinityCategories.CofiberSquare.{u_1} : {X : SSet.{u_1}} →
  {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} →
    SSet.Truncated.Edge.{u_1} x y → Type u_1
@SerrePositivity.InfinityCategories.CofiberSquare.mk.{u_1} : {X : SSet.{u_1}} →
  {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} →
    {f : SSet.Truncated.Edge.{u_1} x y} →
      (toZeroTriangle : SerrePositivity.InfinityCategories.ZeroTriangle.{u_1} X) →
        Eq.{u_1 + 1}
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.squareBottomEdge.{u_1}
              (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u_1} toZeroTriangle))
            ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1}) (SSet.Truncated.Edge.edge.{u_1} f)) →
          SerrePositivity.InfinityCategories.IsPushoutSquare.{u_1}
              (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u_1} toZeroTriangle) →
            SerrePositivity.InfinityCategories.CofiberSquare.{u_1} f
@SerrePositivity.InfinityCategories.FiberSquare.fiber.{u_1} : {X : SSet.{u_1}} →
  {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} →
    {f : SSet.Truncated.Edge.{u_1} x y} →
      SerrePositivity.InfinityCategories.FiberSquare.{u_1} f →
        CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })
@SerrePositivity.InfinityCategories.CofiberSquare.cofiber.{u_1} : {X : SSet.{u_1}} →
  {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} →
    {f : SSet.Truncated.Edge.{u_1} x y} →
      SerrePositivity.InfinityCategories.CofiberSquare.{u_1} f →
        CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })
```

## S2：安定性と有限極限・余極限による判定

前提は各型のとおり。安定性から有限極限・余極限への逆向きは未証明。
S3〜S7 は未完了。対象・集約ビルド成功（1528 jobs）、全 183 宣言／5 モジュールを
標準三公理のみで監査済み。公開型と構成子：

```lean
@SerrePositivity.InfinityCategories.edgeSimplex_source.{u_1} : ∀ {X : SSet.{u_1}}
  {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })}
  (f : SSet.Truncated.Edge.{u_1} x y),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} 1)
      ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1}) (SSet.Truncated.Edge.edge.{u_1} f)))
    ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1}) x)
@SerrePositivity.InfinityCategories.edgeSimplex_target.{u_1} : ∀ {X : SSet.{u_1}}
  {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })}
  (f : SSet.Truncated.Edge.{u_1} x y),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} 0)
      ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1}) (SSet.Truncated.Edge.edge.{u_1} f)))
    ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1}) y)
@SerrePositivity.InfinityCategories.edgeCospan.{u_1} : {X : SSet.{u_1}} →
  {x y z : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} →
    SSet.Truncated.Edge.{u_1} x z →
      SSet.Truncated.Edge.{u_1} y z → Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 2)) X
@SerrePositivity.InfinityCategories.edgeCospan_left.{u_1} : ∀ {X : SSet.{u_1}}
  {x y z : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })}
  (f : SSet.Truncated.Edge.{u_1} x z) (g : SSet.Truncated.Edge.{u_1} y z),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SSet.horn₂₂.ι₀₂.{u_1}
      (SerrePositivity.InfinityCategories.edgeCospan.{u_1} f g))
    ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1}) (SSet.Truncated.Edge.edge.{u_1} f))
@SerrePositivity.InfinityCategories.edgeCospan_right.{u_1} : ∀ {X : SSet.{u_1}}
  {x y z : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })}
  (f : SSet.Truncated.Edge.{u_1} x z) (g : SSet.Truncated.Edge.{u_1} y z),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SSet.horn₂₂.ι₁₂.{u_1}
      (SerrePositivity.InfinityCategories.edgeCospan.{u_1} f g))
    ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1}) (SSet.Truncated.Edge.edge.{u_1} g))
@SerrePositivity.InfinityCategories.edgeSpan.{u_1} : {X : SSet.{u_1}} →
  {x y z : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} →
    SSet.Truncated.Edge.{u_1} x y →
      SSet.Truncated.Edge.{u_1} x z → Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 0)) X
@SerrePositivity.InfinityCategories.edgeSpan_left.{u_1} : ∀ {X : SSet.{u_1}}
  {x y z : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })}
  (f : SSet.Truncated.Edge.{u_1} x y) (g : SSet.Truncated.Edge.{u_1} x z),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SSet.horn₂₀.ι₀₁.{u_1}
      (SerrePositivity.InfinityCategories.edgeSpan.{u_1} f g))
    ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1}) (SSet.Truncated.Edge.edge.{u_1} f))
@SerrePositivity.InfinityCategories.edgeSpan_right.{u_1} : ∀ {X : SSet.{u_1}}
  {x y z : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })}
  (f : SSet.Truncated.Edge.{u_1} x y) (g : SSet.Truncated.Edge.{u_1} x z),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SSet.horn₂₀.ι₀₂.{u_1}
      (SerrePositivity.InfinityCategories.edgeSpan.{u_1} f g))
    ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1}) (SSet.Truncated.Edge.edge.{u_1} g))
@SerrePositivity.InfinityCategories.coneSquare.{u_1} : {X : SSet.{u_1}} →
  {p : Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 2)) X} →
    SerrePositivity.InfinityCategories.JoinCone.{u_1} p →
      Quiver.Hom.{u_1, u_1 + 1}
        (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
        X
@SerrePositivity.InfinityCategories.coneSquare_cospan.{u_1} : ∀ {X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 2)) X}
  (c : SerrePositivity.InfinityCategories.JoinCone.{u_1} p),
  Eq.{u_1 + 1}
    (SerrePositivity.InfinityCategories.pullbackCospan.{u_1} (SerrePositivity.InfinityCategories.coneSquare.{u_1} c)) p
@SerrePositivity.InfinityCategories.coneSquare_isPullback.{u_1} : ∀ {X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 2)) X}
  (c : SerrePositivity.InfinityCategories.JoinCone.{u_1} p),
  SerrePositivity.InfinityCategories.IsLimitCone.{u_1} c →
    SerrePositivity.InfinityCategories.IsPullbackSquare.{u_1} (SerrePositivity.InfinityCategories.coneSquare.{u_1} c)
@SerrePositivity.InfinityCategories.coconeSquare.{u_1} : {X : SSet.{u_1}} →
  {p : Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 0)) X} →
    SerrePositivity.InfinityCategories.JoinCocone.{u_1} p →
      Quiver.Hom.{u_1, u_1 + 1}
        (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
        X
@SerrePositivity.InfinityCategories.coconeSquare_span.{u_1} : ∀ {X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 0)) X}
  (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p),
  Eq.{u_1 + 1}
    (SerrePositivity.InfinityCategories.pushoutSpan.{u_1} (SerrePositivity.InfinityCategories.coconeSquare.{u_1} c)) p
@SerrePositivity.InfinityCategories.coconeSquare_isPushout.{u_1} : ∀ {X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 0)) X}
  (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p),
  SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c →
    SerrePositivity.InfinityCategories.IsPushoutSquare.{u_1} (SerrePositivity.InfinityCategories.coconeSquare.{u_1} c)
@SerrePositivity.InfinityCategories.coneSquare_right.{u_1} : ∀ {X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 2)) X}
  (c : SerrePositivity.InfinityCategories.JoinCone.{u_1} p),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.squareRightEdge.{u_1}
      (SerrePositivity.InfinityCategories.coneSquare.{u_1} c))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SSet.horn₂₂.ι₀₂.{u_1} p)
@SerrePositivity.InfinityCategories.coneSquare_top.{u_1} : ∀ {X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 2)) X}
  (c : SerrePositivity.InfinityCategories.JoinCone.{u_1} p),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.squareTopEdge.{u_1}
      (SerrePositivity.InfinityCategories.coneSquare.{u_1} c))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SSet.horn₂₂.ι₁₂.{u_1} p)
@SerrePositivity.InfinityCategories.coconeSquare_bottom.{u_1} : ∀ {X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 0)) X}
  (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.squareBottomEdge.{u_1}
      (SerrePositivity.InfinityCategories.coconeSquare.{u_1} c))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SSet.horn₂₀.ι₀₁.{u_1} p)
@SerrePositivity.InfinityCategories.coconeSquare_left.{u_1} : ∀ {X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 0)) X}
  (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.squareLeftEdge.{u_1}
      (SerrePositivity.InfinityCategories.coconeSquare.{u_1} c))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SSet.horn₂₀.ι₀₂.{u_1} p)
@SerrePositivity.InfinityCategories.squareTopEdge_source.{u_1} : ∀ {X : SSet.{u_1}}
  (F :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X),
  Eq.{u_1 + 1}
    ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
        (CategoryTheory.SimplicialObject.δ.{u_1, u_1 + 1} X 1))
      (SSet.yonedaEquiv.{u_1}
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.squareTopEdge.{u_1} F)))
    (SerrePositivity.InfinityCategories.squareVertex.{u_1} F 0 1)
@SerrePositivity.InfinityCategories.squareLeftEdge_target.{u_1} : ∀ {X : SSet.{u_1}}
  (F :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X),
  Eq.{u_1 + 1}
    ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
        (CategoryTheory.SimplicialObject.δ.{u_1, u_1 + 1} X 0))
      (SSet.yonedaEquiv.{u_1}
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.squareLeftEdge.{u_1} F)))
    (SerrePositivity.InfinityCategories.squareVertex.{u_1} F 0 1)
@SerrePositivity.InfinityCategories.exists_fiberSquare_of_cospan_limits.{u_1} : ∀ {X : SSet.{u_1}}
  [SerrePositivity.InfinityCategories.HasZeroVertex.{u_1} X],
  (∀ (p : Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 2)) X),
      SerrePositivity.InfinityCategories.HasLimit.{u_1} p) →
    ∀ {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })}
      (f : SSet.Truncated.Edge.{u_1} x y), Nonempty.{u_1 + 1} (SerrePositivity.InfinityCategories.FiberSquare.{u_1} f)
@SerrePositivity.InfinityCategories.exists_cofiberSquare_of_span_colimits.{u_1} : ∀ {X : SSet.{u_1}}
  [SerrePositivity.InfinityCategories.HasZeroVertex.{u_1} X],
  (∀ (p : Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 0)) X),
      SerrePositivity.InfinityCategories.HasColimit.{u_1} p) →
    ∀ {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })}
      (f : SSet.Truncated.Edge.{u_1} x y), Nonempty.{u_1 + 1} (SerrePositivity.InfinityCategories.CofiberSquare.{u_1} f)
SerrePositivity.InfinityCategories.HasFiniteLimits.{u_1} : SSet.{u_1} → Prop
SerrePositivity.InfinityCategories.HasFiniteColimits.{u_1} : SSet.{u_1} → Prop
SerrePositivity.InfinityCategories.IsStable.{u_1} : (X : SSet.{u_1}) → [SSet.Quasicategory.{u_1} X] → Prop
@SerrePositivity.InfinityCategories.chosenFiberSquare.{u_1} : {X : SSet.{u_1}} →
  [inst : SSet.Quasicategory.{u_1} X] →
    [SerrePositivity.InfinityCategories.IsStable.{u_1} X] →
      {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} →
        (f : SSet.Truncated.Edge.{u_1} x y) → SerrePositivity.InfinityCategories.FiberSquare.{u_1} f
@SerrePositivity.InfinityCategories.chosenCofiberSquare.{u_1} : {X : SSet.{u_1}} →
  [inst : SSet.Quasicategory.{u_1} X] →
    [SerrePositivity.InfinityCategories.IsStable.{u_1} X] →
      {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} →
        (f : SSet.Truncated.Edge.{u_1} x y) → SerrePositivity.InfinityCategories.CofiberSquare.{u_1} f
@SerrePositivity.InfinityCategories.IsStable.pushout_of_pullback.{u_1} : ∀ {X : SSet.{u_1}}
  [inst : SSet.Quasicategory.{u_1} X] [SerrePositivity.InfinityCategories.IsStable.{u_1} X]
  (t : SerrePositivity.InfinityCategories.ZeroTriangle.{u_1} X),
  SerrePositivity.InfinityCategories.IsPullbackSquare.{u_1}
      (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u_1} t) →
    SerrePositivity.InfinityCategories.IsPushoutSquare.{u_1}
      (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u_1} t)
@SerrePositivity.InfinityCategories.IsStable.pullback_of_pushout.{u_1} : ∀ {X : SSet.{u_1}}
  [inst : SSet.Quasicategory.{u_1} X] [SerrePositivity.InfinityCategories.IsStable.{u_1} X]
  (t : SerrePositivity.InfinityCategories.ZeroTriangle.{u_1} X),
  SerrePositivity.InfinityCategories.IsPushoutSquare.{u_1}
      (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u_1} t) →
    SerrePositivity.InfinityCategories.IsPullbackSquare.{u_1}
      (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u_1} t)
@SerrePositivity.InfinityCategories.isStable_of_finite_limits_colimits.{u_1} : ∀ {X : SSet.{u_1}}
  [inst : SSet.Quasicategory.{u_1} X] [SerrePositivity.InfinityCategories.HasZeroVertex.{u_1} X]
  [SerrePositivity.InfinityCategories.HasFiniteLimits.{u_1} X]
  [SerrePositivity.InfinityCategories.HasFiniteColimits.{u_1} X],
  (∀
      (F :
        Quiver.Hom.{u_1, u_1 + 1}
          (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
            (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
            (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
          X),
      SerrePositivity.InfinityCategories.IsPullbackSquare.{u_1} F ↔
        SerrePositivity.InfinityCategories.IsPushoutSquare.{u_1} F) →
    SerrePositivity.InfinityCategories.IsStable.{u_1} X
@SerrePositivity.InfinityCategories.HasFiniteLimits.mk.{u_1} : ∀ {X : SSet.{u_1}},
  (∀ {K : SSet.{u_1}} [SSet.Finite.{u_1} K] (p : Quiver.Hom.{u_1, u_1 + 1} K X),
      SerrePositivity.InfinityCategories.HasLimit.{u_1} p) →
    SerrePositivity.InfinityCategories.HasFiniteLimits.{u_1} X
@SerrePositivity.InfinityCategories.HasFiniteColimits.mk.{u_1} : ∀ {X : SSet.{u_1}},
  (∀ {K : SSet.{u_1}} [SSet.Finite.{u_1} K] (p : Quiver.Hom.{u_1, u_1 + 1} K X),
      SerrePositivity.InfinityCategories.HasColimit.{u_1} p) →
    SerrePositivity.InfinityCategories.HasFiniteColimits.{u_1} X
@SerrePositivity.InfinityCategories.IsStable.mk.{u_1} : ∀ {X : SSet.{u_1}} [inst : SSet.Quasicategory.{u_1} X]
  [toHasZeroVertex : SerrePositivity.InfinityCategories.HasZeroVertex.{u_1} X],
  (∀ {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })}
      (f : SSet.Truncated.Edge.{u_1} x y),
      Nonempty.{u_1 + 1} (SerrePositivity.InfinityCategories.FiberSquare.{u_1} f)) →
    (∀ {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })}
        (f : SSet.Truncated.Edge.{u_1} x y),
        Nonempty.{u_1 + 1} (SerrePositivity.InfinityCategories.CofiberSquare.{u_1} f)) →
      (∀ (t : SerrePositivity.InfinityCategories.ZeroTriangle.{u_1} X),
          SerrePositivity.InfinityCategories.IsFiberSequence.{u_1} t ↔
            SerrePositivity.InfinityCategories.IsCofiberSequence.{u_1} t) →
        SerrePositivity.InfinityCategories.IsStable.{u_1} X
```

## S3 の準備：h C の零対象と suspension/loop 四角形

S3 全体は未完了。関手性・選択間の自然同型・ΣΩ の自己同値はまだ主張しない。
対象ビルドと集約ビルド（1600 jobs）、全 268 宣言／8 モジュールの標準三公理監査に成功。
公開型と構成子：

```lean
@SerrePositivity.InfinityCategories.edgeCosliceVertex.{u_1} : {X : SSet.{u_1}} →
  {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} →
    SSet.Truncated.Edge.{u_1} x y →
      CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
        (SerrePositivity.InfinityCategories.sliceUnder.{u_1} ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1}) x))
        (Opposite.op.{1} { len := 0 })
@SerrePositivity.InfinityCategories.edgeCosliceVertex_projection.{u_1} : ∀ {X : SSet.{u_1}}
  {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })}
  (f : SSet.Truncated.Edge.{u_1} x y),
  Eq.{u_1 + 1}
    ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
        (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
          (SerrePositivity.InfinityCategories.sliceUnderProjection.{u_1}
            ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1}) x))
          (Opposite.op.{1} { len := 0 })))
      (SerrePositivity.InfinityCategories.edgeCosliceVertex.{u_1} f))
    y
@SerrePositivity.InfinityCategories.IsInitialVertex.homMk_eq.{u_1} : ∀ {X : SSet.{u_1}}
  [inst : SSet.Quasicategory.{u_1} X]
  {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })},
  SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} x →
    ∀ (f g : SSet.Truncated.Edge.{u_1} x y),
      Eq.{u_1 + 1} (SSet.Truncated.HomotopyCategory₂.homMk.{u_1} f) (SSet.Truncated.HomotopyCategory₂.homMk.{u_1} g)
@SerrePositivity.InfinityCategories.IsInitialVertex.isInitialHo₂.{u_1} : {X : SSet.{u_1}} →
  [inst : SSet.Quasicategory.{u_1} X] →
    {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} →
      SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} x →
        CategoryTheory.Limits.IsInitial.{u_1, u_1} (SSet.Truncated.HomotopyCategory₂.mk.{u_1} x)
@SerrePositivity.InfinityCategories.IsInitialVertex.isInitialHo.{u_1} : {X : SSet.{u_1}} →
  [SSet.Quasicategory.{u_1} X] →
    {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} →
      SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} x →
        CategoryTheory.Limits.IsInitial.{u_1, u_1} (SSet.HomotopyCategory.mk.{u_1} x)
@SerrePositivity.InfinityCategories.IsZeroVertex.isZeroHo.{u_1} : ∀ {X : SSet.{u_1}} [SSet.Quasicategory.{u_1} X]
  {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })},
  SerrePositivity.InfinityCategories.IsZeroVertex.{u_1} x →
    CategoryTheory.Limits.IsZero.{u_1, u_1} (SSet.HomotopyCategory.mk.{u_1} x)
@SerrePositivity.InfinityCategories.hasZeroObject_ho.{u_1} : ∀ {X : SSet.{u_1}} [SSet.Quasicategory.{u_1} X]
  [SerrePositivity.InfinityCategories.HasZeroVertex.{u_1} X],
  CategoryTheory.Limits.HasZeroObject.{u_1, u_1}
    ↑(CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.hoFunctor.{u_1} X)
@SerrePositivity.InfinityCategories.IsInitialVertex.exists_cosliceLift.{u_1} : ∀ {A X : SSet.{u_1}}
  {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })},
  SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} x →
    ∀ (b : Quiver.Hom.{u_1, u_1 + 1} A X),
      ∃ C,
        Eq.{u_1 + 1}
          (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} C
            (SerrePositivity.InfinityCategories.sliceUnderProjection.{u_1}
              ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1}) x)))
          b
@SerrePositivity.InfinityCategories.isInitialVertex_of_isInitialHo.{u_1} : ∀ {X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X] {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })},
  SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} x →
    ∀ (hy : CategoryTheory.Limits.IsInitial.{u_1, u_1} (SSet.HomotopyCategory.mk.{u_1} y)),
      SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} y
@SerrePositivity.InfinityCategories.IsInitialVertex.of_vertexIso.{u_1} : ∀ {X : SSet.{u_1}} [SSet.Quasicategory.{u_1} X]
  {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })},
  SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} x →
    ∀ (e : SerrePositivity.InfinityCategories.VertexIso.{u_1} x y),
      SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} y
@SerrePositivity.InfinityCategories.isInitialVertex_iff_of_vertexIso.{u_1} : ∀ {X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X] {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })}
  (e : SerrePositivity.InfinityCategories.VertexIso.{u_1} x y),
  SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} x ↔
    SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} y
@SerrePositivity.InfinityCategories.IsZeroVertex.of_vertexIso.{u_1} : ∀ {X : SSet.{u_1}} [SSet.Quasicategory.{u_1} X]
  {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })},
  SerrePositivity.InfinityCategories.IsZeroVertex.{u_1} x →
    ∀ (e : SerrePositivity.InfinityCategories.VertexIso.{u_1} x y),
      SerrePositivity.InfinityCategories.IsZeroVertex.{u_1} y
@SerrePositivity.InfinityCategories.IsColimitCone.of_vertexIso.{u_1} : ∀ {K X : SSet.{u_1}} [SSet.Quasicategory.{u_1} X]
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} {c d : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p},
  SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c →
    ∀ (e : SerrePositivity.InfinityCategories.VertexIso.{u_1} c d),
      SerrePositivity.InfinityCategories.IsColimitCone.{u_1} d
@SerrePositivity.InfinityCategories.isColimitCone_iff_of_vertexIso.{u_1} : ∀ {K X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X] {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  {c d : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p}
  (e : SerrePositivity.InfinityCategories.VertexIso.{u_1} c d),
  SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c ↔ SerrePositivity.InfinityCategories.IsColimitCone.{u_1} d
@SerrePositivity.InfinityCategories.squareBottomEdge_source.{u_1} : ∀ {X : SSet.{u_1}}
  (F :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X),
  Eq.{u_1 + 1}
    ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
        (CategoryTheory.SimplicialObject.δ.{u_1, u_1 + 1} X 1))
      (SSet.yonedaEquiv.{u_1}
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.squareBottomEdge.{u_1}
          F)))
    (SerrePositivity.InfinityCategories.squareVertex.{u_1} F 0 0)
@SerrePositivity.InfinityCategories.squareBottomEdge_target.{u_1} : ∀ {X : SSet.{u_1}}
  (F :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X),
  Eq.{u_1 + 1}
    ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
        (CategoryTheory.SimplicialObject.δ.{u_1, u_1 + 1} X 0))
      (SSet.yonedaEquiv.{u_1}
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.squareBottomEdge.{u_1}
          F)))
    (SerrePositivity.InfinityCategories.squareVertex.{u_1} F 1 0)
@SerrePositivity.InfinityCategories.squareRightEdge_source.{u_1} : ∀ {X : SSet.{u_1}}
  (F :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X),
  Eq.{u_1 + 1}
    ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
        (CategoryTheory.SimplicialObject.δ.{u_1, u_1 + 1} X 1))
      (SSet.yonedaEquiv.{u_1}
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.squareRightEdge.{u_1} F)))
    (SerrePositivity.InfinityCategories.squareVertex.{u_1} F 1 0)
@SerrePositivity.InfinityCategories.squareRightEdge_target.{u_1} : ∀ {X : SSet.{u_1}}
  (F :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X),
  Eq.{u_1 + 1}
    ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
        (CategoryTheory.SimplicialObject.δ.{u_1, u_1 + 1} X 0))
      (SSet.yonedaEquiv.{u_1}
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.squareRightEdge.{u_1} F)))
    (SerrePositivity.InfinityCategories.squareVertex.{u_1} F 1 1)
@SerrePositivity.InfinityCategories.SuspensionSquare.{u_1} : {X : SSet.{u_1}} →
  CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 }) → Type u_1
@SerrePositivity.InfinityCategories.LoopSquare.{u_1} : {X : SSet.{u_1}} →
  CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 }) → Type u_1
@SerrePositivity.InfinityCategories.SuspensionSquare.vertex.{u_1} : {X : SSet.{u_1}} →
  {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} →
    SerrePositivity.InfinityCategories.SuspensionSquare.{u_1} x →
      CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })
@SerrePositivity.InfinityCategories.LoopSquare.vertex.{u_1} : {X : SSet.{u_1}} →
  {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} →
    SerrePositivity.InfinityCategories.LoopSquare.{u_1} x →
      CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })
@SerrePositivity.InfinityCategories.chosenSuspensionSquare.{u_1} : {X : SSet.{u_1}} →
  [inst : SSet.Quasicategory.{u_1} X] →
    [SerrePositivity.InfinityCategories.IsStable.{u_1} X] →
      (x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })) →
        SerrePositivity.InfinityCategories.SuspensionSquare.{u_1} x
@SerrePositivity.InfinityCategories.chosenLoopSquare.{u_1} : {X : SSet.{u_1}} →
  [inst : SSet.Quasicategory.{u_1} X] →
    [SerrePositivity.InfinityCategories.IsStable.{u_1} X] →
      (x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })) →
        SerrePositivity.InfinityCategories.LoopSquare.{u_1} x
@SerrePositivity.InfinityCategories.SuspensionSquare.toLoopSquare.{u_1} : {X : SSet.{u_1}} →
  [inst : SSet.Quasicategory.{u_1} X] →
    [SerrePositivity.InfinityCategories.IsStable.{u_1} X] →
      {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} →
        (s : SerrePositivity.InfinityCategories.SuspensionSquare.{u_1} x) →
          SerrePositivity.InfinityCategories.LoopSquare.{u_1}
            (SerrePositivity.InfinityCategories.SuspensionSquare.vertex.{u_1} s)
@SerrePositivity.InfinityCategories.LoopSquare.toSuspensionSquare.{u_1} : {X : SSet.{u_1}} →
  [inst : SSet.Quasicategory.{u_1} X] →
    [SerrePositivity.InfinityCategories.IsStable.{u_1} X] →
      {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} →
        (s : SerrePositivity.InfinityCategories.LoopSquare.{u_1} x) →
          SerrePositivity.InfinityCategories.SuspensionSquare.{u_1}
            (SerrePositivity.InfinityCategories.LoopSquare.vertex.{u_1} s)
@SerrePositivity.InfinityCategories.SuspensionSquare.mk.{u_1} : {X : SSet.{u_1}} →
  {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} →
    (toZeroTriangle : SerrePositivity.InfinityCategories.ZeroTriangle.{u_1} X) →
      Eq.{u_1 + 1}
          (SerrePositivity.InfinityCategories.squareVertex.{u_1}
            (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u_1} toZeroTriangle) 0 0)
          x →
        SerrePositivity.InfinityCategories.IsZeroVertex.{u_1}
            (SerrePositivity.InfinityCategories.squareVertex.{u_1}
              (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u_1} toZeroTriangle) 1 0) →
          SerrePositivity.InfinityCategories.IsPushoutSquare.{u_1}
              (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u_1} toZeroTriangle) →
            SerrePositivity.InfinityCategories.SuspensionSquare.{u_1} x
@SerrePositivity.InfinityCategories.LoopSquare.mk.{u_1} : {X : SSet.{u_1}} →
  {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} →
    (toZeroTriangle : SerrePositivity.InfinityCategories.ZeroTriangle.{u_1} X) →
      Eq.{u_1 + 1}
          (SerrePositivity.InfinityCategories.squareVertex.{u_1}
            (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u_1} toZeroTriangle) 1 1)
          x →
        SerrePositivity.InfinityCategories.IsZeroVertex.{u_1}
            (SerrePositivity.InfinityCategories.squareVertex.{u_1}
              (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u_1} toZeroTriangle) 1 0) →
          SerrePositivity.InfinityCategories.IsPullbackSquare.{u_1}
              (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u_1} toZeroTriangle) →
            SerrePositivity.InfinityCategories.LoopSquare.{u_1} x
```

## S3 の準備：普遍四角形の族と評価

S3 全体は未完了。評価の充満忠実性と、その逆関手による ΣΩ の構成が残る。
対象・集約ビルド（1626 jobs）、全 292 宣言／9 モジュールの標準三公理監査に成功。
並行中の Core の同名補題と衝突しないよう、先の持ち上げ補題を
`IsInitialVertex.exists_stableCosliceLift` に改名した。公開型：

```lean
@SerrePositivity.InfinityCategories.squareDiagram.{u_1} : {X : SSet.{u_1}} →
  CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }) ⟹
        X)
      (Opposite.op.{1} { len := 0 }) →
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X
@SerrePositivity.InfinityCategories.squareDiagram_functorVertex.{u_1} : ∀ {X : SSet.{u_1}}
  (F :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X),
  Eq.{u_1 + 1}
    (SerrePositivity.InfinityCategories.squareDiagram.{u_1} (SerrePositivity.InfinityCategories.functorVertex.{u_1} F))
    F
@SerrePositivity.InfinityCategories.IsSuspensionDiagramVertex.{u_1} : {X : SSet.{u_1}} →
  CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }) ⟹
        X)
      (Opposite.op.{1} { len := 0 }) →
    Prop
@SerrePositivity.InfinityCategories.IsLoopDiagramVertex.{u_1} : {X : SSet.{u_1}} →
  CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }) ⟹
        X)
      (Opposite.op.{1} { len := 0 }) →
    Prop
SerrePositivity.InfinityCategories.suspensionDiagrams.{u_1} : SSet.{u_1} → SSet.{u_1}
SerrePositivity.InfinityCategories.loopDiagrams.{u_1} : SSet.{u_1} → SSet.{u_1}
SerrePositivity.InfinityCategories.suspensionDiagrams_quasicategory.{u_1} : ∀ (X : SSet.{u_1})
  [SSet.Quasicategory.{u_1} X], SSet.Quasicategory.{u_1} (SerrePositivity.InfinityCategories.suspensionDiagrams.{u_1} X)
SerrePositivity.InfinityCategories.loopDiagrams_quasicategory.{u_1} : ∀ (X : SSet.{u_1}) [SSet.Quasicategory.{u_1} X],
  SSet.Quasicategory.{u_1} (SerrePositivity.InfinityCategories.loopDiagrams.{u_1} X)
SerrePositivity.InfinityCategories.suspensionDiagramEvaluation.{u_1} : (X : SSet.{u_1}) →
  Fin 2 → Fin 2 → Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.suspensionDiagrams.{u_1} X) X
SerrePositivity.InfinityCategories.loopDiagramEvaluation.{u_1} : (X : SSet.{u_1}) →
  Fin 2 → Fin 2 → Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.loopDiagrams.{u_1} X) X
@SerrePositivity.InfinityCategories.isSuspensionDiagramVertex_iff_isLoopDiagramVertex.{u_1} : ∀ {X : SSet.{u_1}}
  [inst : SSet.Quasicategory.{u_1} X] [SerrePositivity.InfinityCategories.IsStable.{u_1} X]
  (v :
    CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }) ⟹
        X)
      (Opposite.op.{1} { len := 0 })),
  SerrePositivity.InfinityCategories.IsSuspensionDiagramVertex.{u_1} v ↔
    SerrePositivity.InfinityCategories.IsLoopDiagramVertex.{u_1} v
SerrePositivity.InfinityCategories.suspensionLoopDiagramsIso.{u_1} : (X : SSet.{u_1}) →
  [inst : SSet.Quasicategory.{u_1} X] →
    [SerrePositivity.InfinityCategories.IsStable.{u_1} X] →
      CategoryTheory.Iso.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.suspensionDiagrams.{u_1} X)
        (SerrePositivity.InfinityCategories.loopDiagrams.{u_1} X)
SerrePositivity.InfinityCategories.suspensionLoopDiagramsIso_evaluation.{u_1} : ∀ (X : SSet.{u_1})
  [inst : SSet.Quasicategory.{u_1} X] [inst_1 : SerrePositivity.InfinityCategories.IsStable.{u_1} X] (i j : Fin 2),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.Iso.hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.suspensionLoopDiagramsIso.{u_1} X))
      (SerrePositivity.InfinityCategories.loopDiagramEvaluation.{u_1} X i j))
    (SerrePositivity.InfinityCategories.suspensionDiagramEvaluation.{u_1} X i j)
@SerrePositivity.InfinityCategories.SuspensionSquare.diagramVertex.{u_1} : {X : SSet.{u_1}} →
  {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} →
    SerrePositivity.InfinityCategories.SuspensionSquare.{u_1} x →
      CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (SerrePositivity.InfinityCategories.suspensionDiagrams.{u_1} X)
        (Opposite.op.{1} { len := 0 })
@SerrePositivity.InfinityCategories.LoopSquare.diagramVertex.{u_1} : {X : SSet.{u_1}} →
  {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} →
    SerrePositivity.InfinityCategories.LoopSquare.{u_1} x →
      CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (SerrePositivity.InfinityCategories.loopDiagrams.{u_1} X)
        (Opposite.op.{1} { len := 0 })
@SerrePositivity.InfinityCategories.SuspensionSquare.diagramVertex_evaluation.{u_1} : ∀ {X : SSet.{u_1}}
  {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })}
  (s : SerrePositivity.InfinityCategories.SuspensionSquare.{u_1} x) (i j : Fin 2),
  Eq.{u_1 + 1}
    ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
        (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
          (SerrePositivity.InfinityCategories.suspensionDiagramEvaluation.{u_1} X i j) (Opposite.op.{1} { len := 0 })))
      (SerrePositivity.InfinityCategories.SuspensionSquare.diagramVertex.{u_1} s))
    (SerrePositivity.InfinityCategories.squareVertex.{u_1}
      (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u_1}
        (SerrePositivity.InfinityCategories.SuspensionSquare.toZeroTriangle.{u_1} s))
      i j)
@SerrePositivity.InfinityCategories.LoopSquare.diagramVertex_evaluation.{u_1} : ∀ {X : SSet.{u_1}}
  {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })}
  (s : SerrePositivity.InfinityCategories.LoopSquare.{u_1} x) (i j : Fin 2),
  Eq.{u_1 + 1}
    ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
        (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
          (SerrePositivity.InfinityCategories.loopDiagramEvaluation.{u_1} X i j) (Opposite.op.{1} { len := 0 })))
      (SerrePositivity.InfinityCategories.LoopSquare.diagramVertex.{u_1} s))
    (SerrePositivity.InfinityCategories.squareVertex.{u_1}
      (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u_1}
        (SerrePositivity.InfinityCategories.LoopSquare.toZeroTriangle.{u_1} s))
      i j)
SerrePositivity.InfinityCategories.suspensionDiagramEvaluation_source_surjective.{u_1} : ∀ (X : SSet.{u_1})
  [inst : SSet.Quasicategory.{u_1} X] [SerrePositivity.InfinityCategories.IsStable.{u_1} X],
  Function.Surjective.{u_1 + 1, u_1 + 1}
    ⇑(CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
        (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
          (SerrePositivity.InfinityCategories.suspensionDiagramEvaluation.{u_1} X 0 0) (Opposite.op.{1} { len := 0 })))
SerrePositivity.InfinityCategories.loopDiagramEvaluation_target_surjective.{u_1} : ∀ (X : SSet.{u_1})
  [inst : SSet.Quasicategory.{u_1} X] [SerrePositivity.InfinityCategories.IsStable.{u_1} X],
  Function.Surjective.{u_1 + 1, u_1 + 1}
    ⇑(CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
        (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
          (SerrePositivity.InfinityCategories.loopDiagramEvaluation.{u_1} X 1 1) (Opposite.op.{1} { len := 0 })))
SerrePositivity.InfinityCategories.suspensionDiagramEvaluation_source_essentiallySurjective.{u_1} : ∀ (X : SSet.{u_1})
  [inst : SSet.Quasicategory.{u_1} X] [SerrePositivity.InfinityCategories.IsStable.{u_1} X],
  SerrePositivity.InfinityCategories.IsEssentiallySurjective.{u_1}
    (SerrePositivity.InfinityCategories.suspensionDiagramEvaluation.{u_1} X 0 0)
SerrePositivity.InfinityCategories.loopDiagramEvaluation_target_essentiallySurjective.{u_1} : ∀ (X : SSet.{u_1})
  [inst : SSet.Quasicategory.{u_1} X] [SerrePositivity.InfinityCategories.IsStable.{u_1} X],
  SerrePositivity.InfinityCategories.IsEssentiallySurjective.{u_1}
    (SerrePositivity.InfinityCategories.loopDiagramEvaluation.{u_1} X 1 1)
@SerrePositivity.InfinityCategories.IsInitialVertex.exists_stableCosliceLift.{u_1} : ∀ {A X : SSet.{u_1}}
  {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })},
  SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} x →
    ∀ (b : Quiver.Hom.{u_1, u_1 + 1} A X),
      ∃ C,
        Eq.{u_1 + 1}
          (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} C
            (SerrePositivity.InfinityCategories.sliceUnderProjection.{u_1}
              ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1}) x)))
          b
```

## S3 の準備：余錐の族と左図式を固定した比較

S3 全体は未完了。coslice 比較射自体の同値性、相対充填、ΣΩ の関手性・
選択間の自然同型・自己同値はまだ含めない。対象・集約ビルド（1870 jobs）、
全 312 宣言／11 モジュールの標準三公理監査に成功。公開型：

```lean
SerrePositivity.InfinityCategories.coconeRestriction.{u_1} : (J X : SSet.{u_1}) →
  Quiver.Hom.{u_1, u_1 + 1}
    (SerrePositivity.InfinityCategories.join.{u_1} J
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }) ⟹
      X)
    (J ⟹ X)
@SerrePositivity.InfinityCategories.coconeFamily.{u_1} : {J X : SSet.{u_1}} → Quiver.Hom.{u_1, u_1 + 1} J X → SSet.{u_1}
SerrePositivity.InfinityCategories.coconeRestriction_innerFibration.{u_1} : ∀ (J X : SSet.{u_1})
  [SSet.Quasicategory.{u_1} X],
  SSet.InnerFibration.{u_1} (SerrePositivity.InfinityCategories.coconeRestriction.{u_1} J X)
@SerrePositivity.InfinityCategories.coconeFamily_quasicategory.{u_1} : ∀ {J X : SSet.{u_1}} [SSet.Quasicategory.{u_1} X]
  (p : Quiver.Hom.{u_1, u_1 + 1} J X),
  SSet.Quasicategory.{u_1} (SerrePositivity.InfinityCategories.coconeFamily.{u_1} p)
@SerrePositivity.InfinityCategories.coconeFamilyVertexEquiv.{u_1} : {J X : SSet.{u_1}} →
  (p : Quiver.Hom.{u_1, u_1 + 1} J X) →
    Equiv.{u_1 + 1, u_1 + 1} (SerrePositivity.InfinityCategories.JoinCocone.{u_1} p)
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (SerrePositivity.InfinityCategories.coconeFamily.{u_1} p)
        (Opposite.op.{1} { len := 0 }))
@SerrePositivity.InfinityCategories.cosliceCoconeFamilyUncurry.{u_1} : {J X : SSet.{u_1}} →
  (p : Quiver.Hom.{u_1, u_1 + 1} J X) →
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.join.{u_1} J
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
        (SerrePositivity.InfinityCategories.sliceUnder.{u_1} p))
      X
@SerrePositivity.InfinityCategories.cosliceCoconeFamilyUncurry_fixed.{u_1} : ∀ {J X : SSet.{u_1}}
  (p : Quiver.Hom.{u_1, u_1 + 1} J X),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.joinInl.{u_1} J
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
        (SerrePositivity.InfinityCategories.sliceUnder.{u_1} p))
      (SerrePositivity.InfinityCategories.cosliceCoconeFamilyUncurry.{u_1} p))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.SemiCartesianMonoidalCategory.fst.{u_1, u_1 + 1} J
        (SerrePositivity.InfinityCategories.sliceUnder.{u_1} p))
      p)
@SerrePositivity.InfinityCategories.cosliceCoconeFamilyUncurry_curry_fixed.{u_1} : ∀ {J X : SSet.{u_1}}
  (p : Quiver.Hom.{u_1, u_1 + 1} J X),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalClosed.curry.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.cosliceCoconeFamilyUncurry.{u_1} p))
      (SerrePositivity.InfinityCategories.coconeRestriction.{u_1} J X))
    (SSet.const.{u_1} (SerrePositivity.InfinityCategories.functorVertex.{u_1} p))
@SerrePositivity.InfinityCategories.cosliceCoconeFamilyMap.{u_1} : {J X : SSet.{u_1}} →
  (p : Quiver.Hom.{u_1, u_1 + 1} J X) →
    Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.sliceUnder.{u_1} p)
      (SerrePositivity.InfinityCategories.coconeFamily.{u_1} p)
@SerrePositivity.InfinityCategories.stable_joinTensorRight_naturality.{u_1} : ∀ {C D : SSet.{u_1}}
  (f : Quiver.Hom.{u_1, u_1 + 1} C D) (A B : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.whiskerLeft.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.join.{u_1} A B) f)
      (SerrePositivity.InfinityCategories.joinTensorRight.{u_1} A B D))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.joinTensorRight.{u_1} A B C)
      (SerrePositivity.InfinityCategories.joinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} A)
        (CategoryTheory.MonoidalCategoryStruct.whiskerLeft.{u_1, u_1 + 1} B f)))
@SerrePositivity.InfinityCategories.cosliceCoconeFamilyUncurry_vertex.{u_1} : ∀ {J X : SSet.{u_1}}
  (p : Quiver.Hom.{u_1, u_1 + 1} J X) (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.whiskerLeft.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.join.{u_1} J
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
        ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1}) c))
      (SerrePositivity.InfinityCategories.cosliceCoconeFamilyUncurry.{u_1} p))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.SemiCartesianMonoidalCategory.fst.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.join.{u_1} J
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
      ↑c)
@SerrePositivity.InfinityCategories.cosliceCoconeFamilyMap_app_zero.{u_1} : ∀ {J X : SSet.{u_1}}
  (p : Quiver.Hom.{u_1, u_1 + 1} J X) (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p),
  Eq.{u_1 + 1}
    ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
        (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
          (SerrePositivity.InfinityCategories.cosliceCoconeFamilyMap.{u_1} p) (Opposite.op.{1} { len := 0 })))
      c)
    ((SerrePositivity.InfinityCategories.coconeFamilyVertexEquiv.{u_1} p) c)
SerrePositivity.InfinityCategories.stable_fatJoinInl_mono.{u_1} : ∀ (A B : SSet.{u_1}),
  CategoryTheory.Mono.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} A B)
SerrePositivity.InfinityCategories.isQCatEquivalence_fatJoinComparison_fixedLeftDiagram.{u_1} : ∀ (K A X : SSet.{u_1})
  [inst : SSet.Quasicategory.{u_1} X] (p : Quiver.Hom.{u_1, u_1 + 1} K X),
  SerrePositivity.InfinityCategories.IsQCatEquivalence.{u_1}
    (SerrePositivity.InfinityCategories.fixedDiagramPre.{u_1} (SerrePositivity.InfinityCategories.joinInl.{u_1} K A)
      (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K A)
      (SerrePositivity.InfinityCategories.fatJoinComparison.{u_1} K A) ⋯ p)
```

## S3 の準備：coslice と余錐の関手圏の比較同値

S3 全体は未完了。直接定義の coslice と太い coslice、その後の固定図式上の余錐の族への
比較は同値となり、余極限性を余錐の族の始対象性で判定できる。相対境界充填への接続、
ΣΩ の関手性・自然な選択比較・自己同値と S4〜S7 は残る。
対象・集約ビルド（1913 jobs）、全 406 宣言／24 モジュールの標準三公理監査に成功。
公開型（前提は各型のとおり）：

```lean
SerrePositivity.InfinityCategories.stableFatJoinRightCylinderShuffle.{u_1} : (A B P : SSet.{u_1}) →
  Quiver.Hom.{u_1, u_1 + 1}
    (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1} A
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
        B)
      P)
    (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1} A
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1} B P))
SerrePositivity.InfinityCategories.stableFatJoinTensorRight.{u_1} : (A B P : SSet.{u_1}) →
  Quiver.Hom.{u_1, u_1 + 1}
    (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.fatJoin.{u_1} A B) P)
    (SerrePositivity.InfinityCategories.fatJoin.{u_1} A
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1} B P))
SerrePositivity.InfinityCategories.stableFatJoinTensorRight_inl.{u_1} : ∀ (A B P : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} A B) P)
      (SerrePositivity.InfinityCategories.stableFatJoinTensorRight.{u_1} A B P))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.SemiCartesianMonoidalCategory.fst.{u_1, u_1 + 1} A P)
      (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} A
        (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1} B P)))
SerrePositivity.InfinityCategories.stableFatJoinTensorRight_inr.{u_1} : ∀ (A B P : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.fatJoinInr.{u_1} A B) P)
      (SerrePositivity.InfinityCategories.stableFatJoinTensorRight.{u_1} A B P))
    (SerrePositivity.InfinityCategories.fatJoinInr.{u_1} A
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1} B P))
SerrePositivity.InfinityCategories.stableFatJoinTensorRight_cylinder.{u_1} : ∀ (A B P : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.fatJoinCylinder.{u_1} A B) P)
      (SerrePositivity.InfinityCategories.stableFatJoinTensorRight.{u_1} A B P))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.stableFatJoinRightCylinderShuffle.{u_1} A B P)
      (SerrePositivity.InfinityCategories.fatJoinCylinder.{u_1} A
        (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1} B P)))
@SerrePositivity.InfinityCategories.stableFatJoinTensorRight_naturality.{u_1} : ∀ {P Q : SSet.{u_1}}
  (f : Quiver.Hom.{u_1, u_1 + 1} P Q) (A B : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.whiskerLeft.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.fatJoin.{u_1} A B) f)
      (SerrePositivity.InfinityCategories.stableFatJoinTensorRight.{u_1} A B Q))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.stableFatJoinTensorRight.{u_1} A B P)
      (SerrePositivity.InfinityCategories.fatJoinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} A)
        (CategoryTheory.MonoidalCategoryStruct.whiskerLeft.{u_1, u_1 + 1} B f)))
SerrePositivity.InfinityCategories.stableFatJoinTensorRight_projection.{u_1} : ∀ (A B P : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.stableFatJoinTensorRight.{u_1} A B P)
      (SerrePositivity.InfinityCategories.fatJoinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} A)
        (CategoryTheory.SemiCartesianMonoidalCategory.fst.{u_1, u_1 + 1} B P)))
    (CategoryTheory.SemiCartesianMonoidalCategory.fst.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.fatJoin.{u_1} A B) P)
@SerrePositivity.InfinityCategories.laxCoslice.{u_1} : {K X : SSet.{u_1}} → Quiver.Hom.{u_1, u_1 + 1} K X → SSet.{u_1}
@SerrePositivity.InfinityCategories.laxCoslice_quasicategory.{u_1} : ∀ {K X : SSet.{u_1}} [SSet.Quasicategory.{u_1} X]
  (p : Quiver.Hom.{u_1, u_1 + 1} K X), SSet.Quasicategory.{u_1} (SerrePositivity.InfinityCategories.laxCoslice.{u_1} p)
@SerrePositivity.InfinityCategories.coconeFamilyLaxCosliceMap.{u_1} : {K X : SSet.{u_1}} →
  (p : Quiver.Hom.{u_1, u_1 + 1} K X) →
    Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.coconeFamily.{u_1} p)
      (SerrePositivity.InfinityCategories.laxCoslice.{u_1} p)
@SerrePositivity.InfinityCategories.isQCatEquivalence_coconeFamilyLaxCosliceMap.{u_1} : ∀ {K X : SSet.{u_1}}
  [inst : SSet.Quasicategory.{u_1} X] (p : Quiver.Hom.{u_1, u_1 + 1} K X),
  SerrePositivity.InfinityCategories.IsQCatEquivalence.{u_1}
    (SerrePositivity.InfinityCategories.coconeFamilyLaxCosliceMap.{u_1} p)
@SerrePositivity.InfinityCategories.laxCosliceCurryFamily.{u_1} : {A K X : SSet.{u_1}} →
  Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoin.{u_1} K A) X →
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.fatJoin.{u_1} K
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
        A)
      X
@SerrePositivity.InfinityCategories.laxCosliceCurryFamily_fixed.{u_1} : ∀ {A K X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  (F : Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoin.{u_1} K A) X),
  Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K A) F)
      p →
    Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_1 + 1}
          (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K
            (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
          A)
        (SerrePositivity.InfinityCategories.laxCosliceCurryFamily.{u_1} F))
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (CategoryTheory.SemiCartesianMonoidalCategory.fst.{u_1, u_1 + 1} K A) p)
@SerrePositivity.InfinityCategories.laxCosliceCurry.{u_1} : {A K X : SSet.{u_1}} →
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} →
    (F : Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoin.{u_1} K A) X) →
      Eq.{u_1 + 1}
          (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K A)
            F)
          p →
        Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.laxCoslice.{u_1} p)
SerrePositivity.InfinityCategories.laxCosliceRightInput.{u_1} : (A K : SSet.{u_1}) →
  Quiver.Hom.{u_1, u_1 + 1} A
    (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.fatJoin.{u_1} K
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
      A)
SerrePositivity.InfinityCategories.laxCosliceCylinderInput.{u_1} : (A K : SSet.{u_1}) →
  Quiver.Hom.{u_1, u_1 + 1}
    (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1} K
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      A)
    (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.fatJoin.{u_1} K
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
      A)
SerrePositivity.InfinityCategories.laxCosliceCylinderInput_zero.{u_1} : ∀ (A K : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_1 + 1} SSet.ι₀.{u_1} A)
      (SerrePositivity.InfinityCategories.laxCosliceCylinderInput.{u_1} A K))
    (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
      A)
SerrePositivity.InfinityCategories.laxCosliceCylinderInput_one.{u_1} : ∀ (A K : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_1 + 1} SSet.ι₁.{u_1} A)
      (SerrePositivity.InfinityCategories.laxCosliceCylinderInput.{u_1} A K))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.SemiCartesianMonoidalCategory.snd.{u_1, u_1 + 1} K A)
      (SerrePositivity.InfinityCategories.laxCosliceRightInput.{u_1} A K))
@SerrePositivity.InfinityCategories.laxCosliceFamily_fixed.{u_1} : ∀ {A K X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  (f : Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.laxCoslice.{u_1} p)),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
        A)
      (CategoryTheory.MonoidalClosed.uncurry.{u_1, u_1 + 1}
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} f
          (SerrePositivity.InfinityCategories.vertexFiberι.{u_1}
            (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
              (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1}
                (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K
                  (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 })))
              X)
            (SerrePositivity.InfinityCategories.functorVertex.{u_1} p)))))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.SemiCartesianMonoidalCategory.fst.{u_1, u_1 + 1} K A) p)
@SerrePositivity.InfinityCategories.laxCosliceUncurry.{u_1} : {A K X : SSet.{u_1}} →
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} →
    Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.laxCoslice.{u_1} p) →
      Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoin.{u_1} K A) X
@SerrePositivity.InfinityCategories.laxCosliceUncurry_fixed.{u_1} : ∀ {A K X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  (f : Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.laxCoslice.{u_1} p)),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K A)
      (SerrePositivity.InfinityCategories.laxCosliceUncurry.{u_1} f))
    p
@SerrePositivity.InfinityCategories.laxCosliceUncurry_inr.{u_1} : ∀ {A K X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  (f : Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.laxCoslice.{u_1} p)),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoinInr.{u_1} K A)
      (SerrePositivity.InfinityCategories.laxCosliceUncurry.{u_1} f))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.laxCosliceRightInput.{u_1} A K)
      (CategoryTheory.MonoidalClosed.uncurry.{u_1, u_1 + 1}
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} f
          (SerrePositivity.InfinityCategories.vertexFiberι.{u_1}
            (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
              (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1}
                (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K
                  (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 })))
              X)
            (SerrePositivity.InfinityCategories.functorVertex.{u_1} p)))))
@SerrePositivity.InfinityCategories.laxCosliceUncurry_cylinder.{u_1} : ∀ {A K X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  (f : Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.laxCoslice.{u_1} p)),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoinCylinder.{u_1} K A)
      (SerrePositivity.InfinityCategories.laxCosliceUncurry.{u_1} f))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.laxCosliceCylinderInput.{u_1} A K)
      (CategoryTheory.MonoidalClosed.uncurry.{u_1, u_1 + 1}
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} f
          (SerrePositivity.InfinityCategories.vertexFiberι.{u_1}
            (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
              (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1}
                (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K
                  (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 })))
              X)
            (SerrePositivity.InfinityCategories.functorVertex.{u_1} p)))))
@SerrePositivity.InfinityCategories.laxCosliceRightInput_curryFamily.{u_1} : ∀ {A K X : SSet.{u_1}}
  (F : Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoin.{u_1} K A) X),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.laxCosliceRightInput.{u_1} A K)
      (SerrePositivity.InfinityCategories.laxCosliceCurryFamily.{u_1} F))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoinInr.{u_1} K A) F)
@SerrePositivity.InfinityCategories.laxCosliceCylinderInput_curryFamily.{u_1} : ∀ {A K X : SSet.{u_1}}
  (F : Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoin.{u_1} K A) X),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.laxCosliceCylinderInput.{u_1} A K)
      (SerrePositivity.InfinityCategories.laxCosliceCurryFamily.{u_1} F))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoinCylinder.{u_1} K A) F)
@SerrePositivity.InfinityCategories.laxCosliceUncurry_curry.{u_1} : ∀ {A K X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  (F : Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoin.{u_1} K A) X)
  (hF :
    Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K A) F)
      p),
  Eq.{u_1 + 1}
    (SerrePositivity.InfinityCategories.laxCosliceUncurry.{u_1}
      (SerrePositivity.InfinityCategories.laxCosliceCurry.{u_1} F hF))
    F
@SerrePositivity.InfinityCategories.laxCosliceCurryFamily_uncurry.{u_1} : ∀ {A K X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  (f : Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.laxCoslice.{u_1} p)),
  Eq.{u_1 + 1}
    (SerrePositivity.InfinityCategories.laxCosliceCurryFamily.{u_1}
      (SerrePositivity.InfinityCategories.laxCosliceUncurry.{u_1} f))
    (CategoryTheory.MonoidalClosed.uncurry.{u_1, u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} f
        (SerrePositivity.InfinityCategories.vertexFiberι.{u_1}
          (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
            (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1}
              (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K
                (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 })))
            X)
          (SerrePositivity.InfinityCategories.functorVertex.{u_1} p))))
@SerrePositivity.InfinityCategories.laxCosliceCurry_uncurry.{u_1} : ∀ {A K X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  (f : Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.laxCoslice.{u_1} p)),
  Eq.{u_1 + 1}
    (SerrePositivity.InfinityCategories.laxCosliceCurry.{u_1}
      (SerrePositivity.InfinityCategories.laxCosliceUncurry.{u_1} f) ⋯)
    f
@SerrePositivity.InfinityCategories.laxCosliceHomEquiv.{u_1} : {K X : SSet.{u_1}} →
  (p : Quiver.Hom.{u_1, u_1 + 1} K X) →
    (A : SSet.{u_1}) →
      Equiv.{u_1 + 1, u_1 + 1} (Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.laxCoslice.{u_1} p))
        (Subtype.{u_1 + 1} fun F =>
          Eq.{u_1 + 1}
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K A)
              F)
            p)
@SerrePositivity.InfinityCategories.laxCosliceCurryFamily_precomp.{u_1} : ∀ {A B K X : SSet.{u_1}}
  (a : Quiver.Hom.{u_1, u_1 + 1} A B)
  (F : Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoin.{u_1} K B) X),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.whiskerLeft.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.fatJoin.{u_1} K
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
        a)
      (SerrePositivity.InfinityCategories.laxCosliceCurryFamily.{u_1} F))
    (SerrePositivity.InfinityCategories.laxCosliceCurryFamily.{u_1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.fatJoinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K) a) F))
@SerrePositivity.InfinityCategories.laxCosliceCurry_precomp.{u_1} : ∀ {A B K X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} (a : Quiver.Hom.{u_1, u_1 + 1} A B)
  (F : Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoin.{u_1} K B) X)
  (hF :
    Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K B) F)
      p),
  Eq.{u_1 + 1}
    (SerrePositivity.InfinityCategories.laxCosliceCurry.{u_1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.fatJoinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K) a) F)
      ⋯)
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} a
      (SerrePositivity.InfinityCategories.laxCosliceCurry.{u_1} F hF))
@SerrePositivity.InfinityCategories.laxCosliceUncurry_precomp.{u_1} : ∀ {A B K X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} (a : Quiver.Hom.{u_1, u_1 + 1} A B)
  (f : Quiver.Hom.{u_1, u_1 + 1} B (SerrePositivity.InfinityCategories.laxCoslice.{u_1} p)),
  Eq.{u_1 + 1}
    (SerrePositivity.InfinityCategories.laxCosliceUncurry.{u_1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} a f))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.fatJoinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K) a)
      (SerrePositivity.InfinityCategories.laxCosliceUncurry.{u_1} f))
@SerrePositivity.InfinityCategories.laxCosliceUncurry_injective.{u_1} : ∀ {A K X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} K X},
  Function.Injective.{u_1 + 1, u_1 + 1} SerrePositivity.InfinityCategories.laxCosliceUncurry.{u_1}
SerrePositivity.InfinityCategories.join_right_coproduct_isPushout.{u_1} : ∀ (A B K : SSet.{u_1}),
  CategoryTheory.IsPushout.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.joinInl.{u_1} K A)
    (SerrePositivity.InfinityCategories.joinInl.{u_1} K B)
    (SerrePositivity.InfinityCategories.joinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K)
      CategoryTheory.Limits.coprod.inl.{u_1, u_1 + 1})
    (SerrePositivity.InfinityCategories.joinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K)
      CategoryTheory.Limits.coprod.inr.{u_1, u_1 + 1})
SerrePositivity.InfinityCategories.fatJoin_right_coproduct_isPushout.{u_1} : ∀ (A B K : SSet.{u_1}),
  CategoryTheory.IsPushout.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K A)
    (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K B)
    (SerrePositivity.InfinityCategories.fatJoinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K)
      CategoryTheory.Limits.coprod.inl.{u_1, u_1 + 1})
    (SerrePositivity.InfinityCategories.fatJoinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K)
      CategoryTheory.Limits.coprod.inr.{u_1, u_1 + 1})
SerrePositivity.InfinityCategories.exists_joinRightCylinder_extension_of_relative_homotopy.{u_1} : ∀
  (A K X : SSet.{u_1}) [SSet.Quasicategory.{u_1} X]
  (f g : Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.join.{u_1} K A) X),
  Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.joinInl.{u_1} K A) f)
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.joinInl.{u_1} K A) g) →
    ∀ (H : SSet.Homotopy.{u_1} f g),
      Eq.{u_1 + 1}
          (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
            (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_1 + 1}
              (SerrePositivity.InfinityCategories.joinInl.{u_1} K A)
              (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
            (SSet.RelativeMorphism.Homotopy.h.{u_1} H))
          (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
            (CategoryTheory.SemiCartesianMonoidalCategory.fst.{u_1, u_1 + 1} K
              (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.joinInl.{u_1} K A)
              f)) →
        (∀
            (x :
              CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (SerrePositivity.InfinityCategories.join.{u_1} K A)
                (Opposite.op.{1} { len := 0 })),
            SerrePositivity.InfinityCategories.IsInvertibleEdge.{u_1}
              (SSet.Edge.toTruncated.{u_1}
                (SerrePositivity.InfinityCategories.simplicialHomotopyVertexEdge.{u_1} H x))) →
          ∃ F,
            Eq.{u_1 + 1}
                (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
                  (SerrePositivity.InfinityCategories.joinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K)
                    (SerrePositivity.InfinityCategories.equivalenceCylinderEndpoint.{u_1} A false))
                  F)
                f ∧
              Eq.{u_1 + 1}
                (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
                  (SerrePositivity.InfinityCategories.joinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K)
                    (SerrePositivity.InfinityCategories.equivalenceCylinderEndpoint.{u_1} A true))
                  F)
                g
SerrePositivity.InfinityCategories.exists_fatJoinRightCylinder_extension_of_relative_homotopy.{u_1} : ∀
  (A K X : SSet.{u_1}) [SSet.Quasicategory.{u_1} X]
  (f g : Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoin.{u_1} K A) X),
  Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K A) f)
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K A) g) →
    ∀ (H : SSet.Homotopy.{u_1} f g),
      Eq.{u_1 + 1}
          (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
            (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_1 + 1}
              (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K A)
              (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
            (SSet.RelativeMorphism.Homotopy.h.{u_1} H))
          (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
            (CategoryTheory.SemiCartesianMonoidalCategory.fst.{u_1, u_1 + 1} K
              (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K A)
              f)) →
        (∀
            (x :
              CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoin.{u_1} K A)
                (Opposite.op.{1} { len := 0 })),
            SerrePositivity.InfinityCategories.IsInvertibleEdge.{u_1}
              (SSet.Edge.toTruncated.{u_1}
                (SerrePositivity.InfinityCategories.simplicialHomotopyVertexEdge.{u_1} H x))) →
          ∃ F,
            Eq.{u_1 + 1}
                (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
                  (SerrePositivity.InfinityCategories.fatJoinMap.{u_1}
                    (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K)
                    (SerrePositivity.InfinityCategories.equivalenceCylinderEndpoint.{u_1} A false))
                  F)
                f ∧
              Eq.{u_1 + 1}
                (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
                  (SerrePositivity.InfinityCategories.fatJoinMap.{u_1}
                    (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K)
                    (SerrePositivity.InfinityCategories.equivalenceCylinderEndpoint.{u_1} A true))
                  F)
                g
SerrePositivity.InfinityCategories.isPrecompositionEquivalence_joinRightCylinderProjection.{u_1} : ∀ (A K : SSet.{u_1}),
  SerrePositivity.InfinityCategories.IsPrecompositionEquivalence.{u_1}
    (SerrePositivity.InfinityCategories.joinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K)
      (CategoryTheory.SemiCartesianMonoidalCategory.fst.{u_1, u_1 + 1} A
        SerrePositivity.InfinityCategories.equivalenceInterval.{u_1}))
SerrePositivity.InfinityCategories.joinRightCylinderProjection_epi.{u_1} : ∀ (A K : SSet.{u_1}),
  CategoryTheory.Epi.{u_1, u_1 + 1}
    (SerrePositivity.InfinityCategories.joinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K)
      (CategoryTheory.SemiCartesianMonoidalCategory.fst.{u_1, u_1 + 1} A
        SerrePositivity.InfinityCategories.equivalenceInterval.{u_1}))
SerrePositivity.InfinityCategories.nonempty_fixedDiagramVertexIso_of_joinRightCylinder.{u_1} : ∀ (A K X : SSet.{u_1})
  [SSet.Quasicategory.{u_1} X] (p : Quiver.Hom.{u_1, u_1 + 1} K X)
  (F :
    Quiver.Hom.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.join.{u_1} K
        (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1} A
          SerrePositivity.InfinityCategories.equivalenceInterval.{u_1}))
      X)
  (hF :
    Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.joinInl.{u_1} K
          (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1} A
            SerrePositivity.InfinityCategories.equivalenceInterval.{u_1}))
        F)
      p),
  Nonempty.{u_1 + 1}
    (SerrePositivity.InfinityCategories.VertexIso.{u_1}
      (SerrePositivity.InfinityCategories.fixedDiagramVertex.{u_1}
        (SerrePositivity.InfinityCategories.joinInl.{u_1} K A) p
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
          (SerrePositivity.InfinityCategories.joinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K)
            (SerrePositivity.InfinityCategories.equivalenceCylinderEndpoint.{u_1} A false))
          F)
        ⋯)
      (SerrePositivity.InfinityCategories.fixedDiagramVertex.{u_1}
        (SerrePositivity.InfinityCategories.joinInl.{u_1} K A) p
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
          (SerrePositivity.InfinityCategories.joinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K)
            (SerrePositivity.InfinityCategories.equivalenceCylinderEndpoint.{u_1} A true))
          F)
        ⋯))
SerrePositivity.InfinityCategories.isPrecompositionEquivalence_fatJoinRightCylinderProjection.{u_1} : ∀
  (A K : SSet.{u_1}),
  SerrePositivity.InfinityCategories.IsPrecompositionEquivalence.{u_1}
    (SerrePositivity.InfinityCategories.fatJoinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K)
      (CategoryTheory.SemiCartesianMonoidalCategory.fst.{u_1, u_1 + 1} A
        SerrePositivity.InfinityCategories.equivalenceInterval.{u_1}))
SerrePositivity.InfinityCategories.fatJoinRightCylinderProjection_epi.{u_1} : ∀ (A K : SSet.{u_1}),
  CategoryTheory.Epi.{u_1, u_1 + 1}
    (SerrePositivity.InfinityCategories.fatJoinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K)
      (CategoryTheory.SemiCartesianMonoidalCategory.fst.{u_1, u_1 + 1} A
        SerrePositivity.InfinityCategories.equivalenceInterval.{u_1}))
SerrePositivity.InfinityCategories.nonempty_fixedDiagramVertexIso_of_fatJoinRightCylinder.{u_1} : ∀ (A K X : SSet.{u_1})
  [SSet.Quasicategory.{u_1} X] (p : Quiver.Hom.{u_1, u_1 + 1} K X)
  (F :
    Quiver.Hom.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.fatJoin.{u_1} K
        (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1} A
          SerrePositivity.InfinityCategories.equivalenceInterval.{u_1}))
      X)
  (hF :
    Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K
          (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1} A
            SerrePositivity.InfinityCategories.equivalenceInterval.{u_1}))
        F)
      p),
  Nonempty.{u_1 + 1}
    (SerrePositivity.InfinityCategories.VertexIso.{u_1}
      (SerrePositivity.InfinityCategories.fixedDiagramVertex.{u_1}
        (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K A) p
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
          (SerrePositivity.InfinityCategories.fatJoinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K)
            (SerrePositivity.InfinityCategories.equivalenceCylinderEndpoint.{u_1} A false))
          F)
        ⋯)
      (SerrePositivity.InfinityCategories.fixedDiagramVertex.{u_1}
        (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K A) p
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
          (SerrePositivity.InfinityCategories.fatJoinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K)
            (SerrePositivity.InfinityCategories.equivalenceCylinderEndpoint.{u_1} A true))
          F)
        ⋯))
@SerrePositivity.InfinityCategories.sliceUnderFixedDiagramVertex.{u_1} : {A K X : SSet.{u_1}} →
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} →
    Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.sliceUnder.{u_1} p) →
      CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
        (SerrePositivity.InfinityCategories.vertexFiber.{u_1}
          (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
            (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.joinInl.{u_1} K A)) X)
          (SerrePositivity.InfinityCategories.functorVertex.{u_1} p))
        (Opposite.op.{1} { len := 0 })
@SerrePositivity.InfinityCategories.nonempty_functorIso_of_sliceUnderFixedDiagramVertexIso.{u_1} : ∀
  {A K X : SSet.{u_1}} [SSet.Quasicategory.{u_1} X] {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  (f g : Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.sliceUnder.{u_1} p))
  (e :
    SerrePositivity.InfinityCategories.VertexIso.{u_1}
      (SerrePositivity.InfinityCategories.sliceUnderFixedDiagramVertex.{u_1} f)
      (SerrePositivity.InfinityCategories.sliceUnderFixedDiagramVertex.{u_1} g)),
  Nonempty.{u_1 + 1} (SerrePositivity.InfinityCategories.FunctorIso.{u_1} f g)
@SerrePositivity.InfinityCategories.nonempty_sliceUnderFixedDiagramVertexIso_of_functorIso.{u_1} : ∀
  {A K X : SSet.{u_1}} [SSet.Quasicategory.{u_1} X] {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  {f g : Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.sliceUnder.{u_1} p)}
  (e : SerrePositivity.InfinityCategories.FunctorIso.{u_1} f g),
  Nonempty.{u_1 + 1}
    (SerrePositivity.InfinityCategories.VertexIso.{u_1}
      (SerrePositivity.InfinityCategories.sliceUnderFixedDiagramVertex.{u_1} f)
      (SerrePositivity.InfinityCategories.sliceUnderFixedDiagramVertex.{u_1} g))
@SerrePositivity.InfinityCategories.nonempty_functorIso_iff_sliceUnderFixedDiagramVertexIso.{u_1} : ∀
  {A K X : SSet.{u_1}} [SSet.Quasicategory.{u_1} X] {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  (f g : Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.sliceUnder.{u_1} p)),
  Nonempty.{u_1 + 1} (SerrePositivity.InfinityCategories.FunctorIso.{u_1} f g) ↔
    Nonempty.{u_1 + 1}
      (SerrePositivity.InfinityCategories.VertexIso.{u_1}
        (SerrePositivity.InfinityCategories.sliceUnderFixedDiagramVertex.{u_1} f)
        (SerrePositivity.InfinityCategories.sliceUnderFixedDiagramVertex.{u_1} g))
@SerrePositivity.InfinityCategories.laxCosliceFixedDiagramVertex.{u_1} : {A K X : SSet.{u_1}} →
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} →
    Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.laxCoslice.{u_1} p) →
      CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
        (SerrePositivity.InfinityCategories.vertexFiber.{u_1}
          (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
            (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K A))
            X)
          (SerrePositivity.InfinityCategories.functorVertex.{u_1} p))
        (Opposite.op.{1} { len := 0 })
@SerrePositivity.InfinityCategories.nonempty_functorIso_of_laxCosliceFixedDiagramVertexIso.{u_1} : ∀
  {A K X : SSet.{u_1}} [SSet.Quasicategory.{u_1} X] {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  (f g : Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.laxCoslice.{u_1} p))
  (e :
    SerrePositivity.InfinityCategories.VertexIso.{u_1}
      (SerrePositivity.InfinityCategories.laxCosliceFixedDiagramVertex.{u_1} f)
      (SerrePositivity.InfinityCategories.laxCosliceFixedDiagramVertex.{u_1} g)),
  Nonempty.{u_1 + 1} (SerrePositivity.InfinityCategories.FunctorIso.{u_1} f g)
@SerrePositivity.InfinityCategories.nonempty_laxCosliceFixedDiagramVertexIso_of_functorIso.{u_1} : ∀
  {A K X : SSet.{u_1}} [SSet.Quasicategory.{u_1} X] {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  {f g : Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.laxCoslice.{u_1} p)}
  (e : SerrePositivity.InfinityCategories.FunctorIso.{u_1} f g),
  Nonempty.{u_1 + 1}
    (SerrePositivity.InfinityCategories.VertexIso.{u_1}
      (SerrePositivity.InfinityCategories.laxCosliceFixedDiagramVertex.{u_1} f)
      (SerrePositivity.InfinityCategories.laxCosliceFixedDiagramVertex.{u_1} g))
@SerrePositivity.InfinityCategories.nonempty_functorIso_iff_laxCosliceFixedDiagramVertexIso.{u_1} : ∀
  {A K X : SSet.{u_1}} [SSet.Quasicategory.{u_1} X] {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  (f g : Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.laxCoslice.{u_1} p)),
  Nonempty.{u_1 + 1} (SerrePositivity.InfinityCategories.FunctorIso.{u_1} f g) ↔
    Nonempty.{u_1 + 1}
      (SerrePositivity.InfinityCategories.VertexIso.{u_1}
        (SerrePositivity.InfinityCategories.laxCosliceFixedDiagramVertex.{u_1} f)
        (SerrePositivity.InfinityCategories.laxCosliceFixedDiagramVertex.{u_1} g))
@SerrePositivity.InfinityCategories.sliceUnderFixedDiagramVertexEquiv.{u_1} : {K X : SSet.{u_1}} →
  (p : Quiver.Hom.{u_1, u_1 + 1} K X) →
    (A : SSet.{u_1}) →
      Equiv.{u_1 + 1, u_1 + 1} (Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.sliceUnder.{u_1} p))
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
          (SerrePositivity.InfinityCategories.vertexFiber.{u_1}
            (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
              (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.joinInl.{u_1} K A))
              X)
            (SerrePositivity.InfinityCategories.functorVertex.{u_1} p))
          (Opposite.op.{1} { len := 0 }))
@SerrePositivity.InfinityCategories.laxCosliceFixedDiagramVertexEquiv.{u_1} : {K X : SSet.{u_1}} →
  (p : Quiver.Hom.{u_1, u_1 + 1} K X) →
    (A : SSet.{u_1}) →
      Equiv.{u_1 + 1, u_1 + 1} (Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.laxCoslice.{u_1} p))
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
          (SerrePositivity.InfinityCategories.vertexFiber.{u_1}
            (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
              (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1}
                (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K A))
              X)
            (SerrePositivity.InfinityCategories.functorVertex.{u_1} p))
          (Opposite.op.{1} { len := 0 }))
@SerrePositivity.InfinityCategories.cosliceLaxMap.{u_1} : {K X : SSet.{u_1}} →
  (p : Quiver.Hom.{u_1, u_1 + 1} K X) →
    Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.sliceUnder.{u_1} p)
      (SerrePositivity.InfinityCategories.laxCoslice.{u_1} p)
@SerrePositivity.InfinityCategories.laxCosliceUncurry_comp_cosliceLaxMap.{u_1} : ∀ {A K X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  (f : Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.sliceUnder.{u_1} p)),
  Eq.{u_1 + 1}
    (SerrePositivity.InfinityCategories.laxCosliceUncurry.{u_1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} f (SerrePositivity.InfinityCategories.cosliceLaxMap.{u_1} p)))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.fatJoinComparison.{u_1} K A)
      (SerrePositivity.InfinityCategories.sliceUnderUncurry.{u_1} f))
@SerrePositivity.InfinityCategories.cosliceLaxMap_fixedDiagramVertex.{u_1} : ∀ {A K X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  (f : Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.sliceUnder.{u_1} p)),
  Eq.{u_1 + 1}
    ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
        (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
          (SerrePositivity.InfinityCategories.fixedDiagramPre.{u_1}
            (SerrePositivity.InfinityCategories.joinInl.{u_1} K A)
            (SerrePositivity.InfinityCategories.fatJoinInl.{u_1} K A)
            (SerrePositivity.InfinityCategories.fatJoinComparison.{u_1} K A) ⋯ p)
          (Opposite.op.{1} { len := 0 })))
      (SerrePositivity.InfinityCategories.sliceUnderFixedDiagramVertex.{u_1} f))
    (SerrePositivity.InfinityCategories.laxCosliceFixedDiagramVertex.{u_1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} f (SerrePositivity.InfinityCategories.cosliceLaxMap.{u_1} p)))
@SerrePositivity.InfinityCategories.nonempty_functorIso_of_cosliceLaxMap.{u_1} : ∀ {A K X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X] {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  (f g : Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.sliceUnder.{u_1} p))
  (e :
    SerrePositivity.InfinityCategories.FunctorIso.{u_1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} f (SerrePositivity.InfinityCategories.cosliceLaxMap.{u_1} p))
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} g (SerrePositivity.InfinityCategories.cosliceLaxMap.{u_1} p))),
  Nonempty.{u_1 + 1} (SerrePositivity.InfinityCategories.FunctorIso.{u_1} f g)
@SerrePositivity.InfinityCategories.exists_functorIso_comp_cosliceLaxMap.{u_1} : ∀ {K X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X] (p : Quiver.Hom.{u_1, u_1 + 1} K X) (A : SSet.{u_1})
  (a : Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.laxCoslice.{u_1} p)),
  ∃ f,
    Nonempty.{u_1 + 1}
      (SerrePositivity.InfinityCategories.FunctorIso.{u_1}
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} f (SerrePositivity.InfinityCategories.cosliceLaxMap.{u_1} p))
        a)
@SerrePositivity.InfinityCategories.isQCatEquivalence_cosliceLaxMap.{u_1} : ∀ {K X : SSet.{u_1}}
  [inst : SSet.Quasicategory.{u_1} X] (p : Quiver.Hom.{u_1, u_1 + 1} K X),
  SerrePositivity.InfinityCategories.IsQCatEquivalence.{u_1} (SerrePositivity.InfinityCategories.cosliceLaxMap.{u_1} p)
SerrePositivity.InfinityCategories.stableFatJoinTensorRight_comparison.{u_1} : ∀ (A B P : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.stableFatJoinTensorRight.{u_1} A B P)
      (SerrePositivity.InfinityCategories.fatJoinComparison.{u_1} A
        (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1} B P)))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.fatJoinComparison.{u_1} A B) P)
      (SerrePositivity.InfinityCategories.joinTensorRight.{u_1} A B P))
@SerrePositivity.InfinityCategories.cosliceCoconeFamilyMap_comp_coconeFamilyLaxCosliceMap.{u_1} : ∀ {K X : SSet.{u_1}}
  (p : Quiver.Hom.{u_1, u_1 + 1} K X),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.cosliceCoconeFamilyMap.{u_1} p)
      (SerrePositivity.InfinityCategories.coconeFamilyLaxCosliceMap.{u_1} p))
    (SerrePositivity.InfinityCategories.cosliceLaxMap.{u_1} p)
@SerrePositivity.InfinityCategories.isQCatEquivalence_cosliceCoconeFamilyMap.{u_1} : ∀ {K X : SSet.{u_1}}
  [inst : SSet.Quasicategory.{u_1} X] (p : Quiver.Hom.{u_1, u_1 + 1} K X),
  SerrePositivity.InfinityCategories.IsQCatEquivalence.{u_1}
    (SerrePositivity.InfinityCategories.cosliceCoconeFamilyMap.{u_1} p)
@SerrePositivity.InfinityCategories.QCatEquivalence.map_isInitialVertex.{u_1} : ∀ {X Y : SSet.{u_1}}
  [inst : SSet.Quasicategory.{u_1} X] [inst_1 : SSet.Quasicategory.{u_1} Y]
  (e : SerrePositivity.InfinityCategories.QCatEquivalence.{u_1} X Y)
  {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })},
  SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} x →
    SerrePositivity.InfinityCategories.IsInitialVertex.{u_1}
      ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
          (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
            (SerrePositivity.InfinityCategories.QCatEquivalence.hom.{u_1} e) (Opposite.op.{1} { len := 0 })))
        x)
@SerrePositivity.InfinityCategories.QCatEquivalence.isInitialVertex_iff.{u_1} : ∀ {X Y : SSet.{u_1}}
  [inst : SSet.Quasicategory.{u_1} X] [inst_1 : SSet.Quasicategory.{u_1} Y]
  (e : SerrePositivity.InfinityCategories.QCatEquivalence.{u_1} X Y)
  (x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })),
  SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} x ↔
    SerrePositivity.InfinityCategories.IsInitialVertex.{u_1}
      ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
          (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
            (SerrePositivity.InfinityCategories.QCatEquivalence.hom.{u_1} e) (Opposite.op.{1} { len := 0 })))
        x)
@SerrePositivity.InfinityCategories.isColimitCone_iff_isInitialVertex_coconeFamily.{u_1} : ∀ {K X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X] {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p),
  SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c ↔
    SerrePositivity.InfinityCategories.IsInitialVertex.{u_1}
      ((SerrePositivity.InfinityCategories.coconeFamilyVertexEquiv.{u_1} p) c)
```

## S3 の準備：反転による相対始対象と固定頂点の辺の輸送

S3 全体は未完了。一般の fiber の始対象からの相対充填には、反転した射の
`CocartesianHornFibration` を明示的に仮定する。その仮定を余錐の制限射について
証明する部分は未完了。余錐の終点固定の辺の持ち上げの存在は、頂点上の slice の
right fibration によって構成したが、持ち上げた辺の cartesian 性はまだ含めない。
ΣΩ の関手構成・自己同値と S4〜S7 は残る。Core の境界反転の同型を再利用し、
共有ファイルは変更していない。対象・集約ビルド（1945 jobs）、
全 447 宣言／33 モジュールの標準三公理監査に成功。公開型：

```lean
@SerrePositivity.InfinityCategories.reverseBoundaryMap.{u_1} : {X : SSet.{u_1}} →
  (n : ℕ) →
    Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} (SSet.boundary.{u_1} n)) X →
      Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} (SSet.boundary.{u_1} n)) (SSet.op.{u_1} X)
@SerrePositivity.InfinityCategories.reverseBoundaryMap_restrict.{u_1} : ∀ {X : SSet.{u_1}} (n : ℕ)
  (F :
    Quiver.Hom.{u_1, u_1 + 1} (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := n }) X),
  Eq.{u_1 + 1}
    (SerrePositivity.InfinityCategories.reverseBoundaryMap.{u_1} n
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SSet.Subcomplex.ι.{u_1} (SSet.boundary.{u_1} n)) F))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SSet.Subcomplex.ι.{u_1} (SSet.boundary.{u_1} n))
      (SerrePositivity.InfinityCategories.reverseSimplex.{u_1} n F))
SerrePositivity.InfinityCategories.reverseBoundaryMap_injective.{u_1} : ∀ (X : SSet.{u_1}) (n : ℕ),
  Function.Injective.{u_1 + 1, u_1 + 1} (SerrePositivity.InfinityCategories.reverseBoundaryMap.{u_1} n)
@SerrePositivity.InfinityCategories.reverseBoundaryMap_comp.{u_1} : ∀ {X Y : SSet.{u_1}} (n : ℕ)
  (b : Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} (SSet.boundary.{u_1} n)) X)
  (p : Quiver.Hom.{u_1, u_1 + 1} X Y),
  Eq.{u_1 + 1}
    (SerrePositivity.InfinityCategories.reverseBoundaryMap.{u_1} n
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} b p))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.reverseBoundaryMap.{u_1} n b)
      (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} p))
@SerrePositivity.InfinityCategories.boundaryFiller_of_reverseBoundaryFiller.{u_1} : ∀ {X : SSet.{u_1}} (n : ℕ)
  (b : Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} (SSet.boundary.{u_1} n)) X)
  (F :
    Quiver.Hom.{u_1, u_1 + 1} (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := n })
      (SSet.op.{u_1} X)),
  Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SSet.Subcomplex.ι.{u_1} (SSet.boundary.{u_1} n)) F)
      (SerrePositivity.InfinityCategories.reverseBoundaryMap.{u_1} n b) →
    ∃ G,
      Eq.{u_1 + 1}
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SSet.Subcomplex.ι.{u_1} (SSet.boundary.{u_1} n)) G) b
SerrePositivity.InfinityCategories.boundaryReverseIso_vertex.{u_1} : ∀ (n : ℕ) (i : Fin (HAdd.hAdd.{0, 0, 0} n 2)),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.boundaryVertex.{u_1} n i)
      (CategoryTheory.Iso.hom.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.boundaryReverseIso.{u_1} (HAdd.hAdd.{0, 0, 0} n 1))))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.Iso.inv.{u_1, u_1 + 1} (SSet.stdSimplex.opIso.{u_1} { len := 0 }))
      (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1}
        (SerrePositivity.InfinityCategories.boundaryVertex.{u_1} n i.rev)))
@SerrePositivity.InfinityCategories.reverseBoundaryMap_vertex.{u_1} : ∀ {X : SSet.{u_1}} (n : ℕ)
  (b : Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} (SSet.boundary.{u_1} (HAdd.hAdd.{0, 0, 0} n 1))) X)
  (i : Fin (HAdd.hAdd.{0, 0, 0} n 2)),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.boundaryVertex.{u_1} n i)
      (SerrePositivity.InfinityCategories.reverseBoundaryMap.{u_1} (HAdd.hAdd.{0, 0, 0} n 1) b))
    (SerrePositivity.InfinityCategories.reverseSimplex.{u_1} 0
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.boundaryVertex.{u_1} n i.rev) b))
@SerrePositivity.InfinityCategories.reverseSimplex_vertex.{u_1} : ∀ {X : SSet.{u_1}}
  (x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })),
  Eq.{u_1 + 1}
    (SerrePositivity.InfinityCategories.reverseSimplex.{u_1} 0
      ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1}) x))
    ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1}) ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.opObjEquiv.{u_1}) x))
@SerrePositivity.InfinityCategories.isInitialVertex_of_isTerminalVertex_op.{u_1} : ∀ {X : SSet.{u_1}}
  {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })},
  SerrePositivity.InfinityCategories.IsTerminalVertex.{u_1} ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.opObjEquiv.{u_1}) x) →
    SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} x
@SerrePositivity.InfinityCategories.IsInitialVertex.op_isTerminalVertex.{u_1} : ∀ {X : SSet.{u_1}}
  {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })},
  SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} x →
    SerrePositivity.InfinityCategories.IsTerminalVertex.{u_1} ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.opObjEquiv.{u_1}) x)
@SerrePositivity.InfinityCategories.isInitialVertex_iff_isTerminalVertex_op.{u_1} : ∀ {X : SSet.{u_1}}
  (x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })),
  SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} x ↔
    SerrePositivity.InfinityCategories.IsTerminalVertex.{u_1} ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.opObjEquiv.{u_1}) x)
@SerrePositivity.InfinityCategories.IsTerminalVertex.op_isInitialVertex.{u_1} : ∀ {X : SSet.{u_1}}
  {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })},
  SerrePositivity.InfinityCategories.IsTerminalVertex.{u_1} x →
    SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.opObjEquiv.{u_1}) x)
@SerrePositivity.InfinityCategories.IsZeroVertex.op.{u_1} : ∀ {X : SSet.{u_1}}
  {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })},
  SerrePositivity.InfinityCategories.IsZeroVertex.{u_1} x →
    SerrePositivity.InfinityCategories.IsZeroVertex.{u_1} ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.opObjEquiv.{u_1}) x)
@SerrePositivity.InfinityCategories.InitialBoundaryLifting.{u_1} : {X Y : SSet.{u_1}} →
  Quiver.Hom.{u_1, u_1 + 1} X Y →
    CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 }) → Prop
@SerrePositivity.InfinityCategories.initialBoundaryLifting_of_terminalBoundaryLifting_op.{u_1} : ∀ {E B : SSet.{u_1}}
  (p : Quiver.Hom.{u_1, u_1 + 1} E B)
  (x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} E (Opposite.op.{1} { len := 0 })),
  SerrePositivity.InfinityCategories.TerminalBoundaryLifting.{u_1}
      (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} p)
      ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.opObjEquiv.{u_1}) x) →
    SerrePositivity.InfinityCategories.InitialBoundaryLifting.{u_1} p x
@SerrePositivity.InfinityCategories.InitialBoundaryLifting.isInitialVertex_fiber.{u_1} : ∀ {E B : SSet.{u_1}}
  (p : Quiver.Hom.{u_1, u_1 + 1} E B)
  (b : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} B (Opposite.op.{1} { len := 0 }))
  (x :
    CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (SerrePositivity.InfinityCategories.vertexFiber.{u_1} p b)
      (Opposite.op.{1} { len := 0 })),
  SerrePositivity.InfinityCategories.InitialBoundaryLifting.{u_1} p ↑x →
    SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} x
@SerrePositivity.InfinityCategories.isColimitCone_of_initialBoundaryLifting_coconeRestriction.{u_1} : ∀
  {K X : SSet.{u_1}} [SSet.Quasicategory.{u_1} X] {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p),
  SerrePositivity.InfinityCategories.InitialBoundaryLifting.{u_1}
      (SerrePositivity.InfinityCategories.coconeRestriction.{u_1} K X)
      (SerrePositivity.InfinityCategories.functorVertex.{u_1} ↑c) →
    SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c
@SerrePositivity.InfinityCategories.stablePinchedConstant_op.{u_1} : ∀ {X : SSet.{u_1}}
  (x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })) (n : ℕ),
  Eq.{u_1 + 1}
    (SerrePositivity.InfinityCategories.PinchedHom.constant.{u_1}
      ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.opObjEquiv.{u_1}) x) n)
    ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.opObjEquiv.{u_1})
      (SerrePositivity.InfinityCategories.PinchedHom.constant.{u_1} x n))
@SerrePositivity.InfinityCategories.vertexFiberOpEquiv.{u_1} : {E B : SSet.{u_1}} →
  (p : Quiver.Hom.{u_1, u_1 + 1} E B) →
    (b : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} B (Opposite.op.{1} { len := 0 })) →
      (d : Opposite.{1} SimplexCategory) →
        Equiv.{u_1 + 1, u_1 + 1}
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
            (SSet.op.{u_1} (SerrePositivity.InfinityCategories.vertexFiber.{u_1} p b)) d)
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
            (SerrePositivity.InfinityCategories.vertexFiber.{u_1}
              (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} p)
              ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.opObjEquiv.{u_1}) b))
            d)
@SerrePositivity.InfinityCategories.vertexFiberOpIso.{u_1} : {E B : SSet.{u_1}} →
  (p : Quiver.Hom.{u_1, u_1 + 1} E B) →
    (b : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} B (Opposite.op.{1} { len := 0 })) →
      CategoryTheory.Iso.{u_1, u_1 + 1} (SSet.op.{u_1} (SerrePositivity.InfinityCategories.vertexFiber.{u_1} p b))
        (SerrePositivity.InfinityCategories.vertexFiber.{u_1}
          (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} p)
          ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.opObjEquiv.{u_1}) b))
@SerrePositivity.InfinityCategories.IsInitialVertex.isTerminalVertex_opFiber.{u_1} : ∀ {E B : SSet.{u_1}}
  (p : Quiver.Hom.{u_1, u_1 + 1} E B)
  (b : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} B (Opposite.op.{1} { len := 0 }))
  {x :
    CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (SerrePositivity.InfinityCategories.vertexFiber.{u_1} p b)
      (Opposite.op.{1} { len := 0 })},
  SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} x →
    SerrePositivity.InfinityCategories.IsTerminalVertex.{u_1}
      ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
          (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
            (CategoryTheory.Iso.hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.vertexFiberOpIso.{u_1} p b))
            (Opposite.op.{1} { len := 0 })))
        ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.opObjEquiv.{u_1}) x))
@SerrePositivity.InfinityCategories.initialBoundaryLifting_of_isInitialVertex_fiber_op.{u_1} : ∀ {E B : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} E] [SSet.Quasicategory.{u_1} B] (p : Quiver.Hom.{u_1, u_1 + 1} E B)
  [SerrePositivity.InfinityCategories.CocartesianHornFibration.{u_1}
      (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} p)]
  (b : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} B (Opposite.op.{1} { len := 0 }))
  (x :
    CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (SerrePositivity.InfinityCategories.vertexFiber.{u_1} p b)
      (Opposite.op.{1} { len := 0 })),
  SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} x →
    SerrePositivity.InfinityCategories.InitialBoundaryLifting.{u_1} p ↑x
@SerrePositivity.InfinityCategories.coconeSimplex_lastVertex_of_not_range.{u_1} : ∀ {K : SSet.{u_1}} {n : ℕ},
  ∀
    s ∉
      Set.range.{u_1, u_1 + 1}
        ⇑(CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
            (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
              (SerrePositivity.InfinityCategories.joinInl.{u_1} K
                (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
              (Opposite.op.{1} { len := n }))),
    Eq.{u_1 + 1}
      ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
          (CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1}
            (SerrePositivity.InfinityCategories.join.{u_1} K
              (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
            (Quiver.Hom.op.{0, 0} ({ len := 0 }.const { len := n } (Fin.last n)))))
        s)
      ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
          (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
            (SerrePositivity.InfinityCategories.joinInr.{u_1} K
              (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
            (Opposite.op.{1} { len := 0 })))
        ((Equiv.symm.{u_1 + 1, 1} SSet.stdSimplex.obj₀Equiv.{u_1}) 0))
SerrePositivity.InfinityCategories.stable_hornOneLast_inclusion.{u_1} : ∀ (A : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_1 + 1} (SSet.Subcomplex.ι.{u_1} (SSet.horn.{u_1} 1 1))
      A)
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.SemiCartesianMonoidalCategory.snd.{u_1, u_1 + 1}
        (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 1 1)) A)
      (SerrePositivity.InfinityCategories.prismEndpoint.{u_1} 1 A))
@SerrePositivity.InfinityCategories.stable_rightFibration_lift_prism.{u_1} : ∀ {E B : SSet.{u_1}}
  (p : Quiver.Hom.{u_1, u_1 + 1} E B) [SerrePositivity.InfinityCategories.RightFibration.{u_1} p] (A : SSet.{u_1})
  (f : Quiver.Hom.{u_1, u_1 + 1} A E)
  (H :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }) A)
      B),
  Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.prismEndpoint.{u_1} 1 A) H)
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} f p) →
    ∃ L,
      Eq.{u_1 + 1}
          (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
            (SerrePositivity.InfinityCategories.prismEndpoint.{u_1} 1 A) L)
          f ∧
        Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} L p) H
@SerrePositivity.InfinityCategories.exists_cocone_fixedVertex_transport.{u_1} : ∀ {K X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X]
  (F :
    Quiver.Hom.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.join.{u_1} K
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
      X)
  (H :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }) K)
      X),
  Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.prismEndpoint.{u_1} 1 K) H)
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.joinInl.{u_1} K
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
        F) →
    ∃ G,
      Eq.{u_1 + 1}
          (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
            (SerrePositivity.InfinityCategories.joinInl.{u_1}
              (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
                (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }) K)
              (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
            G)
          H ∧
        Eq.{u_1 + 1}
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
              (SerrePositivity.InfinityCategories.joinMap.{u_1}
                (SerrePositivity.InfinityCategories.prismEndpoint.{u_1} 1 K)
                (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1}
                  (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 })))
              G)
            F ∧
          Eq.{u_1 + 1}
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
              (SerrePositivity.InfinityCategories.joinInr.{u_1}
                (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
                  (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }) K)
                (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
              G)
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
              (SerrePositivity.InfinityCategories.joinInr.{u_1} K
                (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
              F)
SerrePositivity.InfinityCategories.stable_joinTensorLeft_prismEndpoint.{u_1} : ∀ (A B : SSet.{u_1}) (i : Fin 2),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.prismEndpoint.{u_1} i (SerrePositivity.InfinityCategories.join.{u_1} A B))
      (SerrePositivity.InfinityCategories.joinTensorLeft.{u_1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }) A B))
    (SerrePositivity.InfinityCategories.joinMap.{u_1} (SerrePositivity.InfinityCategories.prismEndpoint.{u_1} i A)
      (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} B))
@SerrePositivity.InfinityCategories.exists_cocone_fixedVertex_prism.{u_1} : ∀ {K X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X]
  (F :
    Quiver.Hom.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.join.{u_1} K
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
      X)
  (H :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }) K)
      X),
  Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.prismEndpoint.{u_1} 1 K) H)
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.joinInl.{u_1} K
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
        F) →
    ∃ L,
      Eq.{u_1 + 1}
          (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
            (SerrePositivity.InfinityCategories.prismEndpoint.{u_1} 1
              (SerrePositivity.InfinityCategories.join.{u_1} K
                (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 })))
            L)
          F ∧
        Eq.{u_1 + 1}
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
              (CategoryTheory.MonoidalCategoryStruct.whiskerLeft.{u_1, u_1 + 1}
                (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
                (SerrePositivity.InfinityCategories.joinInl.{u_1} K
                  (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 })))
              L)
            H ∧
          Eq.{u_1 + 1}
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
              (CategoryTheory.MonoidalCategoryStruct.whiskerLeft.{u_1, u_1 + 1}
                (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
                (SerrePositivity.InfinityCategories.joinInr.{u_1} K
                  (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 })))
              L)
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
              (CategoryTheory.SemiCartesianMonoidalCategory.snd.{u_1, u_1 + 1}
                (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
                (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
              (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
                (SerrePositivity.InfinityCategories.joinInr.{u_1} K
                  (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
                F))
SerrePositivity.InfinityCategories.coconeRestriction_hasLiftingProperty_finalVertex.{u_1} : ∀ (K X : SSet.{u_1})
  [SSet.Quasicategory.{u_1} X],
  CategoryTheory.HasLiftingProperty.{u_1, u_1 + 1}
    (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} 0)
    (SerrePositivity.InfinityCategories.coconeRestriction.{u_1} K X)
```

## S3 補助：余錐の cartesian 輸送と相対余極限性

値域の quasicategory 性のみで、余錐制限の反転の cocartesian 輸送と、余極限性 iff 相対始点境界充填を証明した。
ΣΩ の関手性・選択の自然比較・自己同値と S4〜S7 は未完了。
検証：Stable 集約ビルド 1972 jobs 成功、全 471 宣言／39 モジュールの公理監査成功（標準三公理のみ）。

```lean
@SerrePositivity.InfinityCategories.finalHornProduct_fill_boundary.{u_1} : ∀ {X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X] (m n : ℕ)
  (G :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := HAdd.hAdd.{0, 0, 0} m 2 })
        (SSet.Subcomplex.toSSet.{u_1} (SSet.boundary.{u_1} n)))
      X)
  (H :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} (HAdd.hAdd.{0, 0, 0} m 2) (Fin.last (HAdd.hAdd.{0, 0, 0} m 2))))
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := n }))
      X),
  Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_1 + 1}
          (SSet.Subcomplex.ι.{u_1} (SSet.horn.{u_1} (HAdd.hAdd.{0, 0, 0} m 2) (Fin.last (HAdd.hAdd.{0, 0, 0} m 2))))
          (SSet.Subcomplex.toSSet.{u_1} (SSet.boundary.{u_1} n)))
        G)
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (CategoryTheory.MonoidalCategoryStruct.whiskerLeft.{u_1, u_1 + 1}
          (SSet.Subcomplex.toSSet.{u_1}
            (SSet.horn.{u_1} (HAdd.hAdd.{0, 0, 0} m 2) (Fin.last (HAdd.hAdd.{0, 0, 0} m 2))))
          (SSet.Subcomplex.ι.{u_1} (SSet.boundary.{u_1} n)))
        H) →
    SerrePositivity.InfinityCategories.IsInvertibleEdge.{u_1}
        (SerrePositivity.InfinityCategories.edgeOfSimplex.{u_1}
          ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
              (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1} H (Opposite.op.{1} { len := 1 })))
            (Prod.mk.{u_1, u_1} (SerrePositivity.InfinityCategories.finalHornEdge.{u_1} m)
              (SerrePositivity.InfinityCategories.PinchedHom.constant.{u_1}
                ((Equiv.symm.{u_1 + 1, 1} SSet.stdSimplex.obj₀Equiv.{u_1}) (Fin.last n)) 1)))) →
      ∃ F,
        Eq.{u_1 + 1}
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
              (CategoryTheory.MonoidalCategoryStruct.whiskerLeft.{u_1, u_1 + 1}
                (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1}
                  { len := HAdd.hAdd.{0, 0, 0} m 2 })
                (SSet.Subcomplex.ι.{u_1} (SSet.boundary.{u_1} n)))
              F)
            G ∧
          Eq.{u_1 + 1}
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
              (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_1 + 1}
                (SSet.Subcomplex.ι.{u_1}
                  (SSet.horn.{u_1} (HAdd.hAdd.{0, 0, 0} m 2) (Fin.last (HAdd.hAdd.{0, 0, 0} m 2))))
                (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := n }))
              F)
            H
@SerrePositivity.InfinityCategories.finalHornRestriction_lift_of_last_vertices.{u_1} : ∀ {A D X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X] (i : Quiver.Hom.{u_1, u_1 + 1} A D) [CategoryTheory.Mono.{u_1, u_1 + 1} i] (m : ℕ)
  (a :
    Quiver.Hom.{u_1, u_1 + 1} A
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := HAdd.hAdd.{0, 0, 0} m 2 } ⟹ X))
  (b :
    Quiver.Hom.{u_1, u_1 + 1} D
      (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} (HAdd.hAdd.{0, 0, 0} m 2) (Fin.last (HAdd.hAdd.{0, 0, 0} m 2))) ⟹
        X)),
  Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} a
        (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
          (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1}
            (SSet.Subcomplex.ι.{u_1} (SSet.horn.{u_1} (HAdd.hAdd.{0, 0, 0} m 2) (Fin.last (HAdd.hAdd.{0, 0, 0} m 2)))))
          X))
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} i b) →
    (∀ (n : ℕ),
        ∀
          s ∉
            Set.range.{u_1, u_1 + 1}
              ⇑(CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
                  (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1} i (Opposite.op.{1} { len := n }))),
          SerrePositivity.InfinityCategories.IsInvertibleEdge.{u_1}
            (SerrePositivity.InfinityCategories.edgeOfSimplex.{u_1}
              ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
                  (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
                    (CategoryTheory.MonoidalClosed.uncurry.{u_1, u_1 + 1} b) (Opposite.op.{1} { len := 1 })))
                (Prod.mk.{u_1, u_1} (SerrePositivity.InfinityCategories.finalHornEdge.{u_1} m)
                  (SerrePositivity.InfinityCategories.PinchedHom.constant.{u_1}
                    (SerrePositivity.InfinityCategories.simplexLastVertex.{u_1} s) 1))))) →
      ∃ F,
        Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} i F) a ∧
          Eq.{u_1 + 1}
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} F
              (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
                (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1}
                  (SSet.Subcomplex.ι.{u_1}
                    (SSet.horn.{u_1} (HAdd.hAdd.{0, 0, 0} m 2) (Fin.last (HAdd.hAdd.{0, 0, 0} m 2)))))
                X))
            b
SerrePositivity.InfinityCategories.coconeApexEvaluation.{u_1} : (K X : SSet.{u_1}) →
  Quiver.Hom.{u_1, u_1 + 1}
    (SerrePositivity.InfinityCategories.join.{u_1} K
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }) ⟹
      X)
    X
@SerrePositivity.InfinityCategories.isCartesianEdge_coconeRestriction_of_apex.{u_1} : ∀ {K X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X]
  {f g :
    CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
      (SerrePositivity.InfinityCategories.join.{u_1} K
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }) ⟹
        X)
      (Opposite.op.{1} { len := 0 })}
  (e : SSet.Truncated.Edge.{u_1} f g),
  SerrePositivity.InfinityCategories.IsInvertibleEdge.{u_1}
      (SSet.Truncated.Edge.map.{u_1} e
        (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} (SSet.truncation.{u_1} 2)
          (SerrePositivity.InfinityCategories.coconeApexEvaluation.{u_1} K X))) →
    SerrePositivity.InfinityCategories.IsCartesianEdge.{u_1}
      (SerrePositivity.InfinityCategories.coconeRestriction.{u_1} K X) (SSet.Truncated.Edge.edge.{u_1} e)
SerrePositivity.InfinityCategories.exists_cartesian_cocone_lift.{u_1} : ∀ (K X : SSet.{u_1})
  [SSet.Quasicategory.{u_1} X]
  (v :
    CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
      (SerrePositivity.InfinityCategories.join.{u_1} K
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }) ⟹
        X)
      (Opposite.op.{1} { len := 0 }))
  (b : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (K ⟹ X) (Opposite.op.{1} { len := 0 }))
  (a :
    SSet.Truncated.Edge.{u_1} b
      ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
          (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
            (SerrePositivity.InfinityCategories.coconeRestriction.{u_1} K X) (Opposite.op.{1} { len := 0 })))
        v)),
  ∃ w e,
    Eq.{u_1 + 1}
        ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
            (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
              (SerrePositivity.InfinityCategories.coconeRestriction.{u_1} K X) (Opposite.op.{1} { len := 1 })))
          (SSet.Truncated.Edge.edge.{u_1} e))
        (SSet.Truncated.Edge.edge.{u_1} a) ∧
      SerrePositivity.InfinityCategories.IsCartesianEdge.{u_1}
        (SerrePositivity.InfinityCategories.coconeRestriction.{u_1} K X) (SSet.Truncated.Edge.edge.{u_1} e)
SerrePositivity.InfinityCategories.cocartesianHornFibration_coconeRestriction_op.{u_1} : ∀ (K X : SSet.{u_1})
  [SSet.Quasicategory.{u_1} X],
  SerrePositivity.InfinityCategories.CocartesianHornFibration.{u_1}
    (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1}
      (SerrePositivity.InfinityCategories.coconeRestriction.{u_1} K X))
@SerrePositivity.InfinityCategories.IsColimitCone.initialBoundaryLifting.{u_1} : ∀ {K X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X] {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  {c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p},
  SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c →
    SerrePositivity.InfinityCategories.InitialBoundaryLifting.{u_1}
      (SerrePositivity.InfinityCategories.coconeRestriction.{u_1} K X)
      (SerrePositivity.InfinityCategories.functorVertex.{u_1} ↑c)
@SerrePositivity.InfinityCategories.isColimitCone_iff_initialBoundaryLifting.{u_1} : ∀ {K X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X] {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p),
  SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c ↔
    SerrePositivity.InfinityCategories.InitialBoundaryLifting.{u_1}
      (SerrePositivity.InfinityCategories.coconeRestriction.{u_1} K X)
      (SerrePositivity.InfinityCategories.functorVertex.{u_1} ↑c)
```

## S3 補助：普遍余錐の族の選択と比較

相対始対象の全部分圏の正次元境界充填を証明した。各頂点で余極限が存在する任意の図式の族に沿う普遍余錐の射影は trivial Kan fibration であり、厳密な切断と選択間の FunctorIso を得た。
基底に quasicategory 性を要求せず、値域 X の quasicategory 性と族の各頂点での HasColimit のみを仮定する。
ΣΩ の span/cospan の族への適用、評価の充満忠実性、ΣΩ の関手性・自己同値、S4〜S7 は未完了。
検証：Stable 集約ビルド 1974 jobs 成功、全 486 宣言／41 モジュールの公理監査成功（標準三公理のみ）。

```lean
@SerrePositivity.InfinityCategories.relativeInitialVertices.{u_1} : {E B : SSet.{u_1}} →
  Quiver.Hom.{u_1, u_1 + 1} E B → SSet.Subcomplex.{u_1} E
@SerrePositivity.InfinityCategories.relativeInitialProjection.{u_1} : {E B : SSet.{u_1}} →
  (p : Quiver.Hom.{u_1, u_1 + 1} E B) →
    Quiver.Hom.{u_1, u_1 + 1}
      (SSet.Subcomplex.toSSet.{u_1} (SerrePositivity.InfinityCategories.relativeInitialVertices.{u_1} p)) B
@SerrePositivity.InfinityCategories.relativeInitialProjection_hasLiftingProperty_boundary.{u_1} : ∀ {E B : SSet.{u_1}}
  (p : Quiver.Hom.{u_1, u_1 + 1} E B) (n : ℕ),
  CategoryTheory.HasLiftingProperty.{u_1, u_1 + 1}
    (SSet.Subcomplex.ι.{u_1} (SSet.boundary.{u_1} (HAdd.hAdd.{0, 0, 0} n 1)))
    (SerrePositivity.InfinityCategories.relativeInitialProjection.{u_1} p)
@SerrePositivity.InfinityCategories.relativeInitialProjection_trivialKanFibration.{u_1} : ∀ {E B : SSet.{u_1}}
  (p : Quiver.Hom.{u_1, u_1 + 1} E B),
  Function.Surjective.{u_1 + 1, u_1 + 1}
      ⇑(CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
          (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
            (SerrePositivity.InfinityCategories.relativeInitialProjection.{u_1} p) (Opposite.op.{1} { len := 0 }))) →
    SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1}
      (SerrePositivity.InfinityCategories.relativeInitialProjection.{u_1} p)
SerrePositivity.InfinityCategories.colimitCocones.{u_1} : SSet.{u_1} → SSet.{u_1} → SSet.{u_1}
SerrePositivity.InfinityCategories.colimitCocones_quasicategory.{u_1} : ∀ (K X : SSet.{u_1})
  [SSet.Quasicategory.{u_1} X], SSet.Quasicategory.{u_1} (SerrePositivity.InfinityCategories.colimitCocones.{u_1} K X)
@SerrePositivity.InfinityCategories.colimitCocones_vertex_iff.{u_1} : ∀ {K X : SSet.{u_1}} [SSet.Quasicategory.{u_1} X]
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p),
  SerrePositivity.InfinityCategories.InitialBoundaryLifting.{u_1}
      (SerrePositivity.InfinityCategories.coconeRestriction.{u_1} K X)
      (SerrePositivity.InfinityCategories.functorVertex.{u_1} ↑c) ↔
    SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c
SerrePositivity.InfinityCategories.colimitCoconeProjection.{u_1} : (K X : SSet.{u_1}) →
  Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.colimitCocones.{u_1} K X) (K ⟹ X)
@SerrePositivity.InfinityCategories.colimitCoconeProjection_pullback_trivialKanFibration.{u_1} : ∀ {A K X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X] (d : Quiver.Hom.{u_1, u_1 + 1} A (K ⟹ X)),
  (∀ (a : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} A (Opposite.op.{1} { len := 0 })),
      SerrePositivity.InfinityCategories.HasColimit.{u_1}
        ((Equiv.symm.{u_1 + 1, u_1 + 1} (SerrePositivity.InfinityCategories.functorVertexEquiv.{u_1} K X))
          ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
              (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1} d (Opposite.op.{1} { len := 0 })))
            a))) →
    SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1}
      (CategoryTheory.Limits.pullback.snd.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u_1} K X) d)
@SerrePositivity.InfinityCategories.exists_colimitCoconeFamily.{u_1} : ∀ {A K X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X] (d : Quiver.Hom.{u_1, u_1 + 1} A (K ⟹ X)),
  (∀ (a : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} A (Opposite.op.{1} { len := 0 })),
      SerrePositivity.InfinityCategories.HasColimit.{u_1}
        ((Equiv.symm.{u_1 + 1, u_1 + 1} (SerrePositivity.InfinityCategories.functorVertexEquiv.{u_1} K X))
          ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
              (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1} d (Opposite.op.{1} { len := 0 })))
            a))) →
    ∃ f,
      Eq.{u_1 + 1}
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} f
          (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u_1} K X))
        d
@SerrePositivity.InfinityCategories.colimitCoconeFamilyIso.{u_1} : {A K X : SSet.{u_1}} →
  [SSet.Quasicategory.{u_1} X] →
    (d : Quiver.Hom.{u_1, u_1 + 1} A (K ⟹ X)) →
      (∀ (a : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} A (Opposite.op.{1} { len := 0 })),
          SerrePositivity.InfinityCategories.HasColimit.{u_1}
            ((Equiv.symm.{u_1 + 1, u_1 + 1} (SerrePositivity.InfinityCategories.functorVertexEquiv.{u_1} K X))
              ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
                  (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1} d (Opposite.op.{1} { len := 0 })))
                a))) →
        (f g : Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.colimitCocones.{u_1} K X)) →
          Eq.{u_1 + 1}
              (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} f
                (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u_1} K X))
              d →
            Eq.{u_1 + 1}
                (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} g
                  (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u_1} K X))
                d →
              SerrePositivity.InfinityCategories.FunctorIso.{u_1} f g
```

## S3：Suspension 関手と選択の自然な比較

零対象へ向かう辺の始点評価と、suspension 図式の始点評価の trivial Kan fibration 性を証明した。後者の逆と右上の評価から `suspensionFunctor : h C ⥤ h C` を構成した。
同じ始点の族を持つ任意の二つの図式の選択を FunctorIso で比較し、得られる h C 上の関手の自然同型を構成した。任意の指定した SuspensionSquare x の右上と Σx の同型も構成した。
零終点の辺の持ち上げには HasZeroVertex のみ、suspension の主定理には Quasicategory と IsStable を仮定する。
未完了：loop の終点評価の同値性、Ω の関手化、ΣΩ の逆性と自己同値、S4〜S7。S3 全体を完了とは数えない。
検証：Stable 集約ビルド 1981 jobs 成功、全 533 宣言／47 モジュールの公理監査成功（標準三公理のみ）。

```lean
@SerrePositivity.InfinityCategories.stable_interval_lastVertex_of_notMem_firstHorn.{u_1} : ∀ {n : ℕ},
  ∀ s ∉ CategoryTheory.Subfunctor.obj.{u_1, 0, 0} (SSet.horn.{u_1} 1 0) (Opposite.op.{1} { len := n }),
    Eq.{u_1 + 1} (SerrePositivity.InfinityCategories.simplexLastVertex.{u_1} s)
      ((Equiv.symm.{u_1 + 1, 1} SSet.stdSimplex.obj₀Equiv.{u_1}) 1)
@SerrePositivity.InfinityCategories.stable_prism_extend_terminal_boundary.{u_1} : ∀ {X : SSet.{u_1}} (n : ℕ)
  (H :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
        (SSet.Subcomplex.toSSet.{u_1} (SSet.boundary.{u_1} (HAdd.hAdd.{0, 0, 0} n 1))))
      X)
  (F₀ :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := HAdd.hAdd.{0, 0, 0} n 1 }) X),
  Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (SSet.Subcomplex.ι.{u_1} (SSet.boundary.{u_1} (HAdd.hAdd.{0, 0, 0} n 1))) F₀)
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.prismEndpoint.{u_1} 0
          (SSet.Subcomplex.toSSet.{u_1} (SSet.boundary.{u_1} (HAdd.hAdd.{0, 0, 0} n 1))))
        H) →
    (∀
        (v :
          CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
            (SSet.Subcomplex.toSSet.{u_1} (SSet.boundary.{u_1} (HAdd.hAdd.{0, 0, 0} n 1)))
            (Opposite.op.{1} { len := 0 })),
        SerrePositivity.InfinityCategories.IsTerminalVertex.{u_1}
          ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
              (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1} H (Opposite.op.{1} { len := 0 })))
            (Prod.mk.{u_1, u_1} ((Equiv.symm.{u_1 + 1, 1} SSet.stdSimplex.obj₀Equiv.{u_1}) 1) v))) →
      ∃ F,
        Eq.{u_1 + 1}
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
              (CategoryTheory.MonoidalCategoryStruct.whiskerLeft.{u_1, u_1 + 1}
                (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
                (SSet.Subcomplex.ι.{u_1} (SSet.boundary.{u_1} (HAdd.hAdd.{0, 0, 0} n 1))))
              F)
            H ∧
          Eq.{u_1 + 1}
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
              (SerrePositivity.InfinityCategories.prismEndpoint.{u_1} 0
                (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1}
                  { len := HAdd.hAdd.{0, 0, 0} n 1 }))
              F)
            F₀
@SerrePositivity.InfinityCategories.IsZeroTargetArrow.{u_1} : {X : SSet.{u_1}} →
  CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 } ⟹ X)
      (Opposite.op.{1} { len := 0 }) →
    Prop
SerrePositivity.InfinityCategories.zeroTargetArrows.{u_1} : SSet.{u_1} → SSet.{u_1}
SerrePositivity.InfinityCategories.zeroTargetArrowSource.{u_1} : (X : SSet.{u_1}) →
  Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.zeroTargetArrows.{u_1} X) X
SerrePositivity.InfinityCategories.zeroTargetArrowSource_trivialKanFibration.{u_1} : ∀ (X : SSet.{u_1})
  [SerrePositivity.InfinityCategories.HasZeroVertex.{u_1} X],
  SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1}
    (SerrePositivity.InfinityCategories.zeroTargetArrowSource.{u_1} X)
@SerrePositivity.InfinityCategories.stable_intervalFamily_flip_source.{u_1} : ∀ {A X : SSet.{u_1}}
  (L R :
    Quiver.Hom.{u_1, u_1 + 1} A
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 } ⟹ X)),
  Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} L
        (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u_1}
          ((Equiv.symm.{u_1 + 1, 1} SSet.stdSimplex.obj₀Equiv.{u_1}) 0)))
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} R
        (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u_1}
          ((Equiv.symm.{u_1 + 1, 1} SSet.stdSimplex.obj₀Equiv.{u_1}) 0))) →
    Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} 1)
        ((SerrePositivity.InfinityCategories.internalHomFlipHomEquiv.{u_1} A
            (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }) X)
          L))
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} 1)
        ((SerrePositivity.InfinityCategories.internalHomFlipHomEquiv.{u_1} A
            (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }) X)
          R))
@SerrePositivity.InfinityCategories.stable_spanFamilyOfArrows.{u_1} : {A X : SSet.{u_1}} →
  (L R :
      Quiver.Hom.{u_1, u_1 + 1} A
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 } ⟹ X)) →
    Eq.{u_1 + 1}
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} L
          (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u_1}
            ((Equiv.symm.{u_1 + 1, 1} SSet.stdSimplex.obj₀Equiv.{u_1}) 0)))
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} R
          (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u_1}
            ((Equiv.symm.{u_1 + 1, 1} SSet.stdSimplex.obj₀Equiv.{u_1}) 0))) →
      Quiver.Hom.{u_1, u_1 + 1} A (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 0) ⟹ X)
@SerrePositivity.InfinityCategories.stable_spanFamilyOfArrows_left.{u_1} : ∀ {A X : SSet.{u_1}}
  (L R :
    Quiver.Hom.{u_1, u_1 + 1} A
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 } ⟹ X))
  (h :
    Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} L
        (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u_1}
          ((Equiv.symm.{u_1 + 1, 1} SSet.stdSimplex.obj₀Equiv.{u_1}) 0)))
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} R
        (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u_1}
          ((Equiv.symm.{u_1 + 1, 1} SSet.stdSimplex.obj₀Equiv.{u_1}) 0)))),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.stable_spanFamilyOfArrows.{u_1} L R h)
      (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
        (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1} SSet.horn₂₀.ι₀₁.{u_1}) X))
    L
@SerrePositivity.InfinityCategories.stable_spanFamilyOfArrows_right.{u_1} : ∀ {A X : SSet.{u_1}}
  (L R :
    Quiver.Hom.{u_1, u_1 + 1} A
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 } ⟹ X))
  (h :
    Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} L
        (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u_1}
          ((Equiv.symm.{u_1 + 1, 1} SSet.stdSimplex.obj₀Equiv.{u_1}) 0)))
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} R
        (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u_1}
          ((Equiv.symm.{u_1 + 1, 1} SSet.stdSimplex.obj₀Equiv.{u_1}) 0)))),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.stable_spanFamilyOfArrows.{u_1} L R h)
      (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
        (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1} SSet.horn₂₀.ι₀₂.{u_1}) X))
    R
@SerrePositivity.InfinityCategories.stable_spanFamily_hom_ext.{u_1} : ∀ {A X : SSet.{u_1}}
  {f g : Quiver.Hom.{u_1, u_1 + 1} A (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 0) ⟹ X)},
  Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} f
        (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
          (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1} SSet.horn₂₀.ι₀₁.{u_1}) X))
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} g
        (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
          (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1} SSet.horn₂₀.ι₀₁.{u_1}) X)) →
    Eq.{u_1 + 1}
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} f
          (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
            (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1} SSet.horn₂₀.ι₀₂.{u_1}) X))
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} g
          (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
            (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1} SSet.horn₂₀.ι₀₂.{u_1}) X)) →
      Eq.{u_1 + 1} f g
@SerrePositivity.InfinityCategories.stable_pre_evaluateFunctorAt.{u_1} : ∀ {A B X : SSet.{u_1}}
  (i : Quiver.Hom.{u_1, u_1 + 1} A B)
  (v : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} A (Opposite.op.{1} { len := 0 })),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1} (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1} i) X)
      (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u_1} v))
    (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u_1}
      ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
          (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1} i (Opposite.op.{1} { len := 0 })))
        v))
SerrePositivity.InfinityCategories.suspensionDiagramBottomArrow.{u_1} : (X : SSet.{u_1}) →
  Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.suspensionDiagrams.{u_1} X)
    (SerrePositivity.InfinityCategories.zeroTargetArrows.{u_1} X)
SerrePositivity.InfinityCategories.suspensionDiagramLeftArrow.{u_1} : (X : SSet.{u_1}) →
  Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.suspensionDiagrams.{u_1} X)
    (SerrePositivity.InfinityCategories.zeroTargetArrows.{u_1} X)
SerrePositivity.InfinityCategories.suspensionDiagramBottomArrow_source.{u_1} : ∀ (X : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.suspensionDiagramBottomArrow.{u_1} X)
      (SerrePositivity.InfinityCategories.zeroTargetArrowSource.{u_1} X))
    (SerrePositivity.InfinityCategories.suspensionDiagramEvaluation.{u_1} X 0 0)
SerrePositivity.InfinityCategories.suspensionDiagramLeftArrow_source.{u_1} : ∀ (X : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.suspensionDiagramLeftArrow.{u_1} X)
      (SerrePositivity.InfinityCategories.zeroTargetArrowSource.{u_1} X))
    (SerrePositivity.InfinityCategories.suspensionDiagramEvaluation.{u_1} X 0 0)
SerrePositivity.InfinityCategories.suspensionDiagramCoconeFamily.{u_1} : (X : SSet.{u_1}) →
  [SSet.Quasicategory.{u_1} X] →
    Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.suspensionDiagrams.{u_1} X)
      (SerrePositivity.InfinityCategories.colimitCocones.{u_1} (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 0)) X)
SerrePositivity.InfinityCategories.suspensionDiagramCoconeFamily_ι.{u_1} : ∀ (X : SSet.{u_1})
  [inst : SSet.Quasicategory.{u_1} X],
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.suspensionDiagramCoconeFamily.{u_1} X)
      (SSet.Subcomplex.ι.{u_1}
        (SerrePositivity.InfinityCategories.relativeInitialVertices.{u_1}
          (SerrePositivity.InfinityCategories.coconeRestriction.{u_1}
            (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 0)) X))))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SSet.Subcomplex.ι.{u_1}
        (SerrePositivity.InfinityCategories.fullSubcomplexOnVertices.{u_1}
          (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
              (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
              (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }) ⟹
            X)
          SerrePositivity.InfinityCategories.IsSuspensionDiagramVertex.{u_1}))
      (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
        (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1}
          (CategoryTheory.Iso.hom.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.spanCoconeSquareIso.{u_1}))
        X))
SerrePositivity.InfinityCategories.suspensionDiagramCoconeFamily_projection.{u_1} : ∀ (X : SSet.{u_1})
  [inst : SSet.Quasicategory.{u_1} X],
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.suspensionDiagramCoconeFamily.{u_1} X)
      (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u_1}
        (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 0)) X))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SSet.Subcomplex.ι.{u_1}
        (SerrePositivity.InfinityCategories.fullSubcomplexOnVertices.{u_1}
          (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
              (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
              (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }) ⟹
            X)
          SerrePositivity.InfinityCategories.IsSuspensionDiagramVertex.{u_1}))
      (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
        (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.spanSquareBoundary.{u_1})
        X))
SerrePositivity.InfinityCategories.suspensionDiagramEvaluation_source_trivialKanFibration.{u_1} : ∀ (X : SSet.{u_1})
  [inst : SSet.Quasicategory.{u_1} X] [SerrePositivity.InfinityCategories.IsStable.{u_1} X],
  SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1}
    (SerrePositivity.InfinityCategories.suspensionDiagramEvaluation.{u_1} X 0 0)
SerrePositivity.InfinityCategories.suspensionDiagramSourceEquivalence.{u_1} : (X : SSet.{u_1}) →
  [inst : SSet.Quasicategory.{u_1} X] →
    [SerrePositivity.InfinityCategories.IsStable.{u_1} X] →
      SerrePositivity.InfinityCategories.QCatEquivalence.{u_1}
        (SerrePositivity.InfinityCategories.suspensionDiagrams.{u_1} X) X
SerrePositivity.InfinityCategories.suspensionFunctor.{u_1} : (X : SSet.{u_1}) →
  [inst : SSet.Quasicategory.{u_1} X] →
    [SerrePositivity.InfinityCategories.IsStable.{u_1} X] →
      CategoryTheory.Functor.{u_1, u_1, u_1, u_1}
        ↑(CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.hoFunctor.{u_1} X)
        ↑(CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.hoFunctor.{u_1} X)
@SerrePositivity.InfinityCategories.suspensionDiagramFamilyIso.{u_1} : {A X : SSet.{u_1}} →
  [inst : SSet.Quasicategory.{u_1} X] →
    [SerrePositivity.InfinityCategories.IsStable.{u_1} X] →
      (f g : Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.suspensionDiagrams.{u_1} X)) →
        Eq.{u_1 + 1}
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} f
              (SerrePositivity.InfinityCategories.suspensionDiagramEvaluation.{u_1} X 0 0))
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} g
              (SerrePositivity.InfinityCategories.suspensionDiagramEvaluation.{u_1} X 0 0)) →
          SerrePositivity.InfinityCategories.FunctorIso.{u_1} f g
@SerrePositivity.InfinityCategories.suspensionFunctorChoiceIso.{u_1} : {A X : SSet.{u_1}} →
  [inst : SSet.Quasicategory.{u_1} X] →
    [SerrePositivity.InfinityCategories.IsStable.{u_1} X] →
      (f g : Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.suspensionDiagrams.{u_1} X)) →
        Eq.{u_1 + 1}
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} f
              (SerrePositivity.InfinityCategories.suspensionDiagramEvaluation.{u_1} X 0 0))
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} g
              (SerrePositivity.InfinityCategories.suspensionDiagramEvaluation.{u_1} X 0 0)) →
          CategoryTheory.Iso.{u_1, u_1}
            (CategoryTheory.Functor.comp.{u_1, u_1, u_1, u_1, u_1, u_1}
              (CategoryTheory.Cat.Hom.toFunctor.{u_1, u_1}
                (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.hoFunctor.{u_1} f))
              (CategoryTheory.Cat.Hom.toFunctor.{u_1, u_1}
                (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.hoFunctor.{u_1}
                  (SerrePositivity.InfinityCategories.suspensionDiagramEvaluation.{u_1} X 1 1))))
            (CategoryTheory.Functor.comp.{u_1, u_1, u_1, u_1, u_1, u_1}
              (CategoryTheory.Cat.Hom.toFunctor.{u_1, u_1}
                (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.hoFunctor.{u_1} g))
              (CategoryTheory.Cat.Hom.toFunctor.{u_1, u_1}
                (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.hoFunctor.{u_1}
                  (SerrePositivity.InfinityCategories.suspensionDiagramEvaluation.{u_1} X 1 1))))
SerrePositivity.InfinityCategories.suspensionDiagramSourceEquivalence_inv_source.{u_1} : ∀ (X : SSet.{u_1})
  [inst : SSet.Quasicategory.{u_1} X] [inst_1 : SerrePositivity.InfinityCategories.IsStable.{u_1} X],
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.QCatEquivalence.inv.{u_1}
        (SerrePositivity.InfinityCategories.suspensionDiagramSourceEquivalence.{u_1} X))
      (SerrePositivity.InfinityCategories.suspensionDiagramEvaluation.{u_1} X 0 0))
    (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} X)
@SerrePositivity.InfinityCategories.SuspensionSquare.suspensionFunctorObjIso.{u_1} : {X : SSet.{u_1}} →
  [inst : SSet.Quasicategory.{u_1} X] →
    [inst_1 : SerrePositivity.InfinityCategories.IsStable.{u_1} X] →
      {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} →
        (s : SerrePositivity.InfinityCategories.SuspensionSquare.{u_1} x) →
          CategoryTheory.Iso.{u_1, u_1}
            (CategoryTheory.Functor.obj.{u_1, u_1, u_1, u_1}
              (SerrePositivity.InfinityCategories.suspensionFunctor.{u_1} X) (SSet.HomotopyCategory.mk.{u_1} x))
            (SSet.HomotopyCategory.mk.{u_1} (SerrePositivity.InfinityCategories.SuspensionSquare.vertex.{u_1} s))
```

## S3 完了：Loop 関手と suspension の自己同値

零始点の辺の終点評価と loop 図式の終点評価の trivial Kan fibration 性から `loopFunctor` を構成し、選択間の自然同型と任意の LoopSquare の左下との比較を証明した。
安定性による図式の族の同型を介して `suspensionEquivalence` を構成した。その順方向は `suspensionFunctor`、逆方向は `loopFunctor` に厳密に一致し、単位・余単位を自然同型として公開した。
前提：Quasicategory X、IsStable X。零始点の辺の持ち上げのみには HasZeroVertex X だけを仮定する。S3 は完了。S4〜S7 と有限極限・余極限による判定の逆向きは未完了。
検証：Stable 集約ビルド 2000 jobs 成功、全 604 宣言／56 モジュールの公理監査成功（標準三公理のみ）。

```lean
@SerrePositivity.InfinityCategories.stable_exists_extension_of_initial_first_vertices.{u_1} : ∀ {B X : SSet.{u_1}}
  (A : SSet.Subcomplex.{u_1} B)
  (hA :
    ∀ (v : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} B (Opposite.op.{1} { len := 0 })),
      Membership.mem.{u_1, u_1} (CategoryTheory.Subfunctor.obj.{u_1, 0, 0} A (Opposite.op.{1} { len := 0 })) v)
  (a : Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} A) X),
  (∀ (n : ℕ),
      ∀ s ∉ CategoryTheory.Subfunctor.obj.{u_1, 0, 0} A (Opposite.op.{1} { len := HAdd.hAdd.{0, 0, 0} n 1 }),
        SerrePositivity.InfinityCategories.IsInitialVertex.{u_1}
          ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
              (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1} a (Opposite.op.{1} { len := 0 })))
            (Subtype.mk.{u_1 + 1} (SerrePositivity.InfinityCategories.simplexFirstVertex.{u_1} s) ⋯))) →
    ∃ F, Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SSet.Subcomplex.ι.{u_1} A) F) a
@SerrePositivity.InfinityCategories.stable_interval_firstVertex_of_notMem_lastHorn.{u_1} : ∀ {n : ℕ},
  ∀ s ∉ CategoryTheory.Subfunctor.obj.{u_1, 0, 0} (SSet.horn.{u_1} 1 1) (Opposite.op.{1} { len := n }),
    Eq.{u_1 + 1} (SerrePositivity.InfinityCategories.simplexFirstVertex.{u_1} s)
      ((Equiv.symm.{u_1 + 1, 1} SSet.stdSimplex.obj₀Equiv.{u_1}) 0)
@SerrePositivity.InfinityCategories.stable_simplexFirstVertex_prod.{u_1} : ∀ {A B : SSet.{u_1}} {n : ℕ}
  (s :
    CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1} A B)
      (Opposite.op.{1} { len := n })),
  Eq.{u_1 + 1} (SerrePositivity.InfinityCategories.simplexFirstVertex.{u_1} s)
    (Prod.mk.{u_1, u_1} (SerrePositivity.InfinityCategories.simplexFirstVertex.{u_1} s.1)
      (SerrePositivity.InfinityCategories.simplexFirstVertex.{u_1} s.2))
@SerrePositivity.InfinityCategories.stable_prism_extend_initial_boundary.{u_1} : ∀ {X : SSet.{u_1}} (n : ℕ)
  (H :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
        (SSet.Subcomplex.toSSet.{u_1} (SSet.boundary.{u_1} (HAdd.hAdd.{0, 0, 0} n 1))))
      X)
  (F₁ :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := HAdd.hAdd.{0, 0, 0} n 1 }) X),
  Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (SSet.Subcomplex.ι.{u_1} (SSet.boundary.{u_1} (HAdd.hAdd.{0, 0, 0} n 1))) F₁)
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.prismEndpoint.{u_1} 1
          (SSet.Subcomplex.toSSet.{u_1} (SSet.boundary.{u_1} (HAdd.hAdd.{0, 0, 0} n 1))))
        H) →
    (∀
        (v :
          CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
            (SSet.Subcomplex.toSSet.{u_1} (SSet.boundary.{u_1} (HAdd.hAdd.{0, 0, 0} n 1)))
            (Opposite.op.{1} { len := 0 })),
        SerrePositivity.InfinityCategories.IsInitialVertex.{u_1}
          ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
              (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1} H (Opposite.op.{1} { len := 0 })))
            (Prod.mk.{u_1, u_1} ((Equiv.symm.{u_1 + 1, 1} SSet.stdSimplex.obj₀Equiv.{u_1}) 0) v))) →
      ∃ F,
        Eq.{u_1 + 1}
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
              (CategoryTheory.MonoidalCategoryStruct.whiskerLeft.{u_1, u_1 + 1}
                (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
                (SSet.Subcomplex.ι.{u_1} (SSet.boundary.{u_1} (HAdd.hAdd.{0, 0, 0} n 1))))
              F)
            H ∧
          Eq.{u_1 + 1}
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
              (SerrePositivity.InfinityCategories.prismEndpoint.{u_1} 1
                (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1}
                  { len := HAdd.hAdd.{0, 0, 0} n 1 }))
              F)
            F₁
@SerrePositivity.InfinityCategories.IsZeroSourceArrow.{u_1} : {X : SSet.{u_1}} →
  CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 } ⟹ X)
      (Opposite.op.{1} { len := 0 }) →
    Prop
SerrePositivity.InfinityCategories.zeroSourceArrows.{u_1} : SSet.{u_1} → SSet.{u_1}
SerrePositivity.InfinityCategories.zeroSourceArrowTarget.{u_1} : (X : SSet.{u_1}) →
  Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.zeroSourceArrows.{u_1} X) X
SerrePositivity.InfinityCategories.zeroSourceArrowTarget_trivialKanFibration.{u_1} : ∀ (X : SSet.{u_1})
  [SerrePositivity.InfinityCategories.HasZeroVertex.{u_1} X],
  SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1}
    (SerrePositivity.InfinityCategories.zeroSourceArrowTarget.{u_1} X)
@SerrePositivity.InfinityCategories.relativeTerminalVertices.{u_1} : {E B : SSet.{u_1}} →
  Quiver.Hom.{u_1, u_1 + 1} E B → SSet.Subcomplex.{u_1} E
@SerrePositivity.InfinityCategories.relativeTerminalProjection.{u_1} : {E B : SSet.{u_1}} →
  (p : Quiver.Hom.{u_1, u_1 + 1} E B) →
    Quiver.Hom.{u_1, u_1 + 1}
      (SSet.Subcomplex.toSSet.{u_1} (SerrePositivity.InfinityCategories.relativeTerminalVertices.{u_1} p)) B
@SerrePositivity.InfinityCategories.relativeTerminalProjection_hasLiftingProperty_boundary.{u_1} : ∀ {E B : SSet.{u_1}}
  (p : Quiver.Hom.{u_1, u_1 + 1} E B) (n : ℕ),
  CategoryTheory.HasLiftingProperty.{u_1, u_1 + 1}
    (SSet.Subcomplex.ι.{u_1} (SSet.boundary.{u_1} (HAdd.hAdd.{0, 0, 0} n 1)))
    (SerrePositivity.InfinityCategories.relativeTerminalProjection.{u_1} p)
SerrePositivity.InfinityCategories.limitCones.{u_1} : SSet.{u_1} → SSet.{u_1} → SSet.{u_1}
SerrePositivity.InfinityCategories.limitConeProjection.{u_1} : (K X : SSet.{u_1}) →
  Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.limitCones.{u_1} K X) (K ⟹ X)
@SerrePositivity.InfinityCategories.stable_intervalFamily_flip_target.{u_1} : ∀ {A X : SSet.{u_1}}
  (L R :
    Quiver.Hom.{u_1, u_1 + 1} A
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 } ⟹ X)),
  Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} L
        (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u_1}
          ((Equiv.symm.{u_1 + 1, 1} SSet.stdSimplex.obj₀Equiv.{u_1}) 1)))
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} R
        (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u_1}
          ((Equiv.symm.{u_1 + 1, 1} SSet.stdSimplex.obj₀Equiv.{u_1}) 1))) →
    Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} 0)
        ((SerrePositivity.InfinityCategories.internalHomFlipHomEquiv.{u_1} A
            (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }) X)
          L))
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} 0)
        ((SerrePositivity.InfinityCategories.internalHomFlipHomEquiv.{u_1} A
            (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }) X)
          R))
@SerrePositivity.InfinityCategories.stable_cospanFamilyOfArrows.{u_1} : {A X : SSet.{u_1}} →
  (L R :
      Quiver.Hom.{u_1, u_1 + 1} A
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 } ⟹ X)) →
    Eq.{u_1 + 1}
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} L
          (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u_1}
            ((Equiv.symm.{u_1 + 1, 1} SSet.stdSimplex.obj₀Equiv.{u_1}) 1)))
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} R
          (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u_1}
            ((Equiv.symm.{u_1 + 1, 1} SSet.stdSimplex.obj₀Equiv.{u_1}) 1))) →
      Quiver.Hom.{u_1, u_1 + 1} A (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 2) ⟹ X)
@SerrePositivity.InfinityCategories.stable_cospanFamilyOfArrows_left.{u_1} : ∀ {A X : SSet.{u_1}}
  (L R :
    Quiver.Hom.{u_1, u_1 + 1} A
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 } ⟹ X))
  (h :
    Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} L
        (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u_1}
          ((Equiv.symm.{u_1 + 1, 1} SSet.stdSimplex.obj₀Equiv.{u_1}) 1)))
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} R
        (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u_1}
          ((Equiv.symm.{u_1 + 1, 1} SSet.stdSimplex.obj₀Equiv.{u_1}) 1)))),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.stable_cospanFamilyOfArrows.{u_1} L R h)
      (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
        (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1} SSet.horn₂₂.ι₀₂.{u_1}) X))
    L
@SerrePositivity.InfinityCategories.stable_cospanFamilyOfArrows_right.{u_1} : ∀ {A X : SSet.{u_1}}
  (L R :
    Quiver.Hom.{u_1, u_1 + 1} A
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 } ⟹ X))
  (h :
    Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} L
        (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u_1}
          ((Equiv.symm.{u_1 + 1, 1} SSet.stdSimplex.obj₀Equiv.{u_1}) 1)))
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} R
        (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u_1}
          ((Equiv.symm.{u_1 + 1, 1} SSet.stdSimplex.obj₀Equiv.{u_1}) 1)))),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.stable_cospanFamilyOfArrows.{u_1} L R h)
      (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
        (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1} SSet.horn₂₂.ι₁₂.{u_1}) X))
    R
@SerrePositivity.InfinityCategories.stable_cospanFamily_hom_ext.{u_1} : ∀ {A X : SSet.{u_1}}
  {f g : Quiver.Hom.{u_1, u_1 + 1} A (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 2) ⟹ X)},
  Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} f
        (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
          (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1} SSet.horn₂₂.ι₀₂.{u_1}) X))
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} g
        (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
          (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1} SSet.horn₂₂.ι₀₂.{u_1}) X)) →
    Eq.{u_1 + 1}
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} f
          (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
            (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1} SSet.horn₂₂.ι₁₂.{u_1}) X))
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} g
          (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
            (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1} SSet.horn₂₂.ι₁₂.{u_1}) X)) →
      Eq.{u_1 + 1} f g
SerrePositivity.InfinityCategories.loopDiagramRightArrow.{u_1} : (X : SSet.{u_1}) →
  Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.loopDiagrams.{u_1} X)
    (SerrePositivity.InfinityCategories.zeroSourceArrows.{u_1} X)
SerrePositivity.InfinityCategories.loopDiagramTopArrow.{u_1} : (X : SSet.{u_1}) →
  Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.loopDiagrams.{u_1} X)
    (SerrePositivity.InfinityCategories.zeroSourceArrows.{u_1} X)
SerrePositivity.InfinityCategories.loopDiagramRightArrow_target.{u_1} : ∀ (X : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.loopDiagramRightArrow.{u_1} X)
      (SerrePositivity.InfinityCategories.zeroSourceArrowTarget.{u_1} X))
    (SerrePositivity.InfinityCategories.loopDiagramEvaluation.{u_1} X 1 1)
SerrePositivity.InfinityCategories.loopDiagramTopArrow_target.{u_1} : ∀ (X : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.loopDiagramTopArrow.{u_1} X)
      (SerrePositivity.InfinityCategories.zeroSourceArrowTarget.{u_1} X))
    (SerrePositivity.InfinityCategories.loopDiagramEvaluation.{u_1} X 1 1)
SerrePositivity.InfinityCategories.loopDiagramConeFamily.{u_1} : (X : SSet.{u_1}) →
  [SSet.Quasicategory.{u_1} X] →
    Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.loopDiagrams.{u_1} X)
      (SerrePositivity.InfinityCategories.limitCones.{u_1} (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 2)) X)
SerrePositivity.InfinityCategories.loopDiagramConeFamily_ι.{u_1} : ∀ (X : SSet.{u_1})
  [inst : SSet.Quasicategory.{u_1} X],
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.loopDiagramConeFamily.{u_1} X)
      (SSet.Subcomplex.ι.{u_1}
        (SerrePositivity.InfinityCategories.relativeTerminalVertices.{u_1}
          (SerrePositivity.InfinityCategories.coneRestriction.{u_1} (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 2))
            X))))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SSet.Subcomplex.ι.{u_1}
        (SerrePositivity.InfinityCategories.fullSubcomplexOnVertices.{u_1}
          (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
              (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
              (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }) ⟹
            X)
          SerrePositivity.InfinityCategories.IsLoopDiagramVertex.{u_1}))
      (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
        (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1}
          (CategoryTheory.Iso.hom.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.cospanConeSquareIso.{u_1}))
        X))
SerrePositivity.InfinityCategories.loopDiagramConeFamily_projection.{u_1} : ∀ (X : SSet.{u_1})
  [inst : SSet.Quasicategory.{u_1} X],
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.loopDiagramConeFamily.{u_1} X)
      (SerrePositivity.InfinityCategories.limitConeProjection.{u_1} (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 2))
        X))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SSet.Subcomplex.ι.{u_1}
        (SerrePositivity.InfinityCategories.fullSubcomplexOnVertices.{u_1}
          (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
              (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
              (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }) ⟹
            X)
          SerrePositivity.InfinityCategories.IsLoopDiagramVertex.{u_1}))
      (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
        (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.cospanSquareBoundary.{u_1})
        X))
SerrePositivity.InfinityCategories.loopDiagramEvaluation_target_trivialKanFibration.{u_1} : ∀ (X : SSet.{u_1})
  [inst : SSet.Quasicategory.{u_1} X] [SerrePositivity.InfinityCategories.IsStable.{u_1} X],
  SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1}
    (SerrePositivity.InfinityCategories.loopDiagramEvaluation.{u_1} X 1 1)
SerrePositivity.InfinityCategories.loopDiagramTargetEquivalence.{u_1} : (X : SSet.{u_1}) →
  [inst : SSet.Quasicategory.{u_1} X] →
    [SerrePositivity.InfinityCategories.IsStable.{u_1} X] →
      SerrePositivity.InfinityCategories.QCatEquivalence.{u_1} (SerrePositivity.InfinityCategories.loopDiagrams.{u_1} X)
        X
SerrePositivity.InfinityCategories.loopFunctor.{u_1} : (X : SSet.{u_1}) →
  [inst : SSet.Quasicategory.{u_1} X] →
    [SerrePositivity.InfinityCategories.IsStable.{u_1} X] →
      CategoryTheory.Functor.{u_1, u_1, u_1, u_1}
        ↑(CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.hoFunctor.{u_1} X)
        ↑(CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.hoFunctor.{u_1} X)
@SerrePositivity.InfinityCategories.loopDiagramFamilyIso.{u_1} : {A X : SSet.{u_1}} →
  [inst : SSet.Quasicategory.{u_1} X] →
    [SerrePositivity.InfinityCategories.IsStable.{u_1} X] →
      (f g : Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.loopDiagrams.{u_1} X)) →
        Eq.{u_1 + 1}
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} f
              (SerrePositivity.InfinityCategories.loopDiagramEvaluation.{u_1} X 1 1))
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} g
              (SerrePositivity.InfinityCategories.loopDiagramEvaluation.{u_1} X 1 1)) →
          SerrePositivity.InfinityCategories.FunctorIso.{u_1} f g
@SerrePositivity.InfinityCategories.loopFunctorChoiceIso.{u_1} : {A X : SSet.{u_1}} →
  [inst : SSet.Quasicategory.{u_1} X] →
    [SerrePositivity.InfinityCategories.IsStable.{u_1} X] →
      (f g : Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.loopDiagrams.{u_1} X)) →
        Eq.{u_1 + 1}
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} f
              (SerrePositivity.InfinityCategories.loopDiagramEvaluation.{u_1} X 1 1))
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} g
              (SerrePositivity.InfinityCategories.loopDiagramEvaluation.{u_1} X 1 1)) →
          CategoryTheory.Iso.{u_1, u_1}
            (CategoryTheory.Functor.comp.{u_1, u_1, u_1, u_1, u_1, u_1}
              (CategoryTheory.Cat.Hom.toFunctor.{u_1, u_1}
                (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.hoFunctor.{u_1} f))
              (CategoryTheory.Cat.Hom.toFunctor.{u_1, u_1}
                (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.hoFunctor.{u_1}
                  (SerrePositivity.InfinityCategories.loopDiagramEvaluation.{u_1} X 0 0))))
            (CategoryTheory.Functor.comp.{u_1, u_1, u_1, u_1, u_1, u_1}
              (CategoryTheory.Cat.Hom.toFunctor.{u_1, u_1}
                (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.hoFunctor.{u_1} g))
              (CategoryTheory.Cat.Hom.toFunctor.{u_1, u_1}
                (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.hoFunctor.{u_1}
                  (SerrePositivity.InfinityCategories.loopDiagramEvaluation.{u_1} X 0 0))))
SerrePositivity.InfinityCategories.loopDiagramTargetEquivalence_inv_target.{u_1} : ∀ (X : SSet.{u_1})
  [inst : SSet.Quasicategory.{u_1} X] [inst_1 : SerrePositivity.InfinityCategories.IsStable.{u_1} X],
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.QCatEquivalence.inv.{u_1}
        (SerrePositivity.InfinityCategories.loopDiagramTargetEquivalence.{u_1} X))
      (SerrePositivity.InfinityCategories.loopDiagramEvaluation.{u_1} X 1 1))
    (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} X)
@SerrePositivity.InfinityCategories.LoopSquare.loopFunctorObjIso.{u_1} : {X : SSet.{u_1}} →
  [inst : SSet.Quasicategory.{u_1} X] →
    [inst_1 : SerrePositivity.InfinityCategories.IsStable.{u_1} X] →
      {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} →
        (s : SerrePositivity.InfinityCategories.LoopSquare.{u_1} x) →
          CategoryTheory.Iso.{u_1, u_1}
            (CategoryTheory.Functor.obj.{u_1, u_1, u_1, u_1} (SerrePositivity.InfinityCategories.loopFunctor.{u_1} X)
              (SSet.HomotopyCategory.mk.{u_1} x))
            (SSet.HomotopyCategory.mk.{u_1} (SerrePositivity.InfinityCategories.LoopSquare.vertex.{u_1} s))
SerrePositivity.InfinityCategories.suspensionLoopDiagramEquivalence.{u_1} : (X : SSet.{u_1}) →
  [inst : SSet.Quasicategory.{u_1} X] →
    [SerrePositivity.InfinityCategories.IsStable.{u_1} X] →
      SerrePositivity.InfinityCategories.QCatEquivalence.{u_1}
        (SerrePositivity.InfinityCategories.suspensionDiagrams.{u_1} X)
        (SerrePositivity.InfinityCategories.loopDiagrams.{u_1} X)
SerrePositivity.InfinityCategories.suspensionQCatEquivalence.{u_1} : (X : SSet.{u_1}) →
  [inst : SSet.Quasicategory.{u_1} X] →
    [SerrePositivity.InfinityCategories.IsStable.{u_1} X] → SerrePositivity.InfinityCategories.QCatEquivalence.{u_1} X X
SerrePositivity.InfinityCategories.suspensionQCatEquivalence_hom.{u_1} : ∀ (X : SSet.{u_1})
  [inst : SSet.Quasicategory.{u_1} X] [inst_1 : SerrePositivity.InfinityCategories.IsStable.{u_1} X],
  Eq.{u_1 + 1}
    (SerrePositivity.InfinityCategories.QCatEquivalence.hom.{u_1}
      (SerrePositivity.InfinityCategories.suspensionQCatEquivalence.{u_1} X))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.QCatEquivalence.inv.{u_1}
        (SerrePositivity.InfinityCategories.suspensionDiagramSourceEquivalence.{u_1} X))
      (SerrePositivity.InfinityCategories.suspensionDiagramEvaluation.{u_1} X 1 1))
SerrePositivity.InfinityCategories.suspensionQCatEquivalence_inv.{u_1} : ∀ (X : SSet.{u_1})
  [inst : SSet.Quasicategory.{u_1} X] [inst_1 : SerrePositivity.InfinityCategories.IsStable.{u_1} X],
  Eq.{u_1 + 1}
    (SerrePositivity.InfinityCategories.QCatEquivalence.inv.{u_1}
      (SerrePositivity.InfinityCategories.suspensionQCatEquivalence.{u_1} X))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.QCatEquivalence.inv.{u_1}
        (SerrePositivity.InfinityCategories.loopDiagramTargetEquivalence.{u_1} X))
      (SerrePositivity.InfinityCategories.loopDiagramEvaluation.{u_1} X 0 0))
SerrePositivity.InfinityCategories.suspensionQCatEquivalence_ho_functor.{u_1} : ∀ (X : SSet.{u_1})
  [inst : SSet.Quasicategory.{u_1} X] [inst_1 : SerrePositivity.InfinityCategories.IsStable.{u_1} X],
  Eq.{u_1 + 1}
    (CategoryTheory.Equivalence.functor.{u_1, u_1, u_1, u_1}
      (SerrePositivity.InfinityCategories.QCatEquivalence.toHoEquivalence.{u_1}
        (SerrePositivity.InfinityCategories.suspensionQCatEquivalence.{u_1} X)))
    (SerrePositivity.InfinityCategories.suspensionFunctor.{u_1} X)
SerrePositivity.InfinityCategories.suspensionQCatEquivalence_ho_inverse.{u_1} : ∀ (X : SSet.{u_1})
  [inst : SSet.Quasicategory.{u_1} X] [inst_1 : SerrePositivity.InfinityCategories.IsStable.{u_1} X],
  Eq.{u_1 + 1}
    (CategoryTheory.Equivalence.inverse.{u_1, u_1, u_1, u_1}
      (SerrePositivity.InfinityCategories.QCatEquivalence.toHoEquivalence.{u_1}
        (SerrePositivity.InfinityCategories.suspensionQCatEquivalence.{u_1} X)))
    (SerrePositivity.InfinityCategories.loopFunctor.{u_1} X)
SerrePositivity.InfinityCategories.suspensionEquivalence.{u_1} : (X : SSet.{u_1}) →
  [inst : SSet.Quasicategory.{u_1} X] →
    [SerrePositivity.InfinityCategories.IsStable.{u_1} X] →
      CategoryTheory.Equivalence.{u_1, u_1, u_1, u_1}
        ↑(CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.hoFunctor.{u_1} X)
        ↑(CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.hoFunctor.{u_1} X)
SerrePositivity.InfinityCategories.suspensionEquivalence_functor.{u_1} : ∀ (X : SSet.{u_1})
  [inst : SSet.Quasicategory.{u_1} X] [inst_1 : SerrePositivity.InfinityCategories.IsStable.{u_1} X],
  Eq.{u_1 + 1}
    (CategoryTheory.Equivalence.functor.{u_1, u_1, u_1, u_1}
      (SerrePositivity.InfinityCategories.suspensionEquivalence.{u_1} X))
    (SerrePositivity.InfinityCategories.suspensionFunctor.{u_1} X)
SerrePositivity.InfinityCategories.suspensionEquivalence_inverse.{u_1} : ∀ (X : SSet.{u_1})
  [inst : SSet.Quasicategory.{u_1} X] [inst_1 : SerrePositivity.InfinityCategories.IsStable.{u_1} X],
  Eq.{u_1 + 1}
    (CategoryTheory.Equivalence.inverse.{u_1, u_1, u_1, u_1}
      (SerrePositivity.InfinityCategories.suspensionEquivalence.{u_1} X))
    (SerrePositivity.InfinityCategories.loopFunctor.{u_1} X)
SerrePositivity.InfinityCategories.suspensionLoopUnitIso.{u_1} : (X : SSet.{u_1}) →
  [inst : SSet.Quasicategory.{u_1} X] →
    [inst_1 : SerrePositivity.InfinityCategories.IsStable.{u_1} X] →
      CategoryTheory.Iso.{u_1, u_1}
        (CategoryTheory.Functor.id.{u_1, u_1}
          ↑(CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.hoFunctor.{u_1} X))
        (CategoryTheory.Functor.comp.{u_1, u_1, u_1, u_1, u_1, u_1}
          (SerrePositivity.InfinityCategories.suspensionFunctor.{u_1} X)
          (SerrePositivity.InfinityCategories.loopFunctor.{u_1} X))
SerrePositivity.InfinityCategories.loopSuspensionCounitIso.{u_1} : (X : SSet.{u_1}) →
  [inst : SSet.Quasicategory.{u_1} X] →
    [inst_1 : SerrePositivity.InfinityCategories.IsStable.{u_1} X] →
      CategoryTheory.Iso.{u_1, u_1}
        (CategoryTheory.Functor.comp.{u_1, u_1, u_1, u_1, u_1, u_1}
          (SerrePositivity.InfinityCategories.loopFunctor.{u_1} X)
          (SerrePositivity.InfinityCategories.suspensionFunctor.{u_1} X))
        (CategoryTheory.Functor.id.{u_1, u_1}
          ↑(CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.hoFunctor.{u_1} X))
```

## S4 着手：貼り合わせの長方形と三つの四角形

`Δ[2] × Δ[1]` の余面 2・0・1 を左・右・外側の四角形とし、共有辺・外側二辺・上下の二単体への制限の厳密な一致を証明した。値域 X の quasicategory 性は仮定しない。
HTT の原典表記は Lemma 4.4.2.1（https://people.math.harvard.edu/~lurie/papers/HTT.pdf 、PDF p.313）。貼り合わせの普遍性は未完了で、部分長方形上の slice/coslice の制限の比較が残る。三角構造・TR1〜TR4・長完全列・完全関手・D7 は未完了。
検証：対象ビルド 1526 jobs・Stable 集約ビルド 2001 jobs 成功、全 613 宣言／57 モジュールの公理監査成功（標準三公理のみ）。

```lean
@SerrePositivity.InfinityCategories.pastingSquare.{u_1} : {X : SSet.{u_1}} →
  Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X →
    Fin 3 →
      Quiver.Hom.{u_1, u_1 + 1}
        (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
        X
@SerrePositivity.InfinityCategories.pastingBottomTriangle.{u_1} : {X : SSet.{u_1}} →
  Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X →
    Quiver.Hom.{u_1, u_1 + 1} (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 }) X
@SerrePositivity.InfinityCategories.pastingTopTriangle.{u_1} : {X : SSet.{u_1}} →
  Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X →
    Quiver.Hom.{u_1, u_1 + 1} (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 }) X
@SerrePositivity.InfinityCategories.pastingSquare_sharedEdge.{u_1} : ∀ {X : SSet.{u_1}}
  (F :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.squareRightEdge.{u_1}
      (SerrePositivity.InfinityCategories.pastingSquare.{u_1} F 2))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.squareLeftEdge.{u_1}
      (SerrePositivity.InfinityCategories.pastingSquare.{u_1} F 0))
@SerrePositivity.InfinityCategories.pastingSquare_outer_leftEdge.{u_1} : ∀ {X : SSet.{u_1}}
  (F :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.squareLeftEdge.{u_1}
      (SerrePositivity.InfinityCategories.pastingSquare.{u_1} F 1))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.squareLeftEdge.{u_1}
      (SerrePositivity.InfinityCategories.pastingSquare.{u_1} F 2))
@SerrePositivity.InfinityCategories.pastingSquare_outer_rightEdge.{u_1} : ∀ {X : SSet.{u_1}}
  (F :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.squareRightEdge.{u_1}
      (SerrePositivity.InfinityCategories.pastingSquare.{u_1} F 1))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.squareRightEdge.{u_1}
      (SerrePositivity.InfinityCategories.pastingSquare.{u_1} F 0))
@SerrePositivity.InfinityCategories.pastingSquare_bottomEdge.{u_1} : ∀ {X : SSet.{u_1}}
  (F :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X)
  (i : Fin 3),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.squareBottomEdge.{u_1}
      (SerrePositivity.InfinityCategories.pastingSquare.{u_1} F i))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} i)
      (SerrePositivity.InfinityCategories.pastingBottomTriangle.{u_1} F))
@SerrePositivity.InfinityCategories.pastingSquare_topEdge.{u_1} : ∀ {X : SSet.{u_1}}
  (F :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X)
  (i : Fin 3),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.squareTopEdge.{u_1}
      (SerrePositivity.InfinityCategories.pastingSquare.{u_1} F i))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} i)
      (SerrePositivity.InfinityCategories.pastingTopTriangle.{u_1} F))
```

## S4：部分長方形の右側への cofinal な制限

右上の終端角を除いた五頂点図式 `pastingCorner` と、その右側の三頂点部分 `pastingRightSpan` を構成した。横座標を max(x,t) に写し、右の部分を全時刻で固定する prism から、その包含の right anodyne 性を証明した。
固定部分を持つ prism の収縮から right anodyne 性を得る一般補題も証明した。F1 の部分複体への coslice 制限定理と同型による制限を再利用し、任意の right anodyne な単射への拡張を証明した。余極限性を保ち反映することを得て、部分長方形に適用した。Core・F1 の既存宣言は変更していない。
値域に Quasicategory を仮定する余錐の比較と、値域を選ぶ前の包含の right anodyne 性を区別する。これを貼り合わせ定理全体の完成とは数えない。
残る工程：右側の三頂点部分の標準 span との同定、長方形の join 表示、左四角形の普遍性を使う外側図式への coslice の比較、引き戻しへの双対化、三角構造（前加法性・整数シフト・TR1〜TR4を含む）、S5〜S7。
検証：PastingCofinality 対象ビルド 1921 jobs・Stable 集約ビルド 2006 jobs 成功。全 645 宣言／62 モジュールの公理監査成功（標準三公理のみ）。

```lean
@SerrePositivity.InfinityCategories.sliceUnderRestrict_trivialKanFibration.{u_1} : ∀ {K₀ K X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X] (p : Quiver.Hom.{u_1, u_1 + 1} K X) (f : Quiver.Hom.{u_1, u_1 + 1} K₀ K)
  [CategoryTheory.Mono.{u_1, u_1 + 1} f],
  SerrePositivity.InfinityCategories.rightAnodyneExtensions.{u_1} f →
    SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1}
      (SerrePositivity.InfinityCategories.sliceUnderRestrict.{u_1} p f)
@SerrePositivity.InfinityCategories.stable_rightAnodyneExtensions_of_prism_retraction.{u_1} : ∀ {B : SSet.{u_1}}
  (A : SSet.Subcomplex.{u_1} B) (r : Quiver.Hom.{u_1, u_1 + 1} B (SSet.Subcomplex.toSSet.{u_1} A)),
  Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SSet.Subcomplex.ι.{u_1} A) r)
      (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} A)) →
    ∀
      (H :
        Quiver.Hom.{u_1, u_1 + 1}
          (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
            (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }) B)
          B),
      Eq.{u_1 + 1}
          (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
            (SerrePositivity.InfinityCategories.prismEndpoint.{u_1} 0 B) H)
          (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} B) →
        Eq.{u_1 + 1}
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
              (SerrePositivity.InfinityCategories.prismEndpoint.{u_1} 1 B) H)
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} r (SSet.Subcomplex.ι.{u_1} A)) →
          Eq.{u_1 + 1}
              (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
                (CategoryTheory.MonoidalCategoryStruct.whiskerLeft.{u_1, u_1 + 1}
                  (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
                  (SSet.Subcomplex.ι.{u_1} A))
                H)
              (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
                (CategoryTheory.SemiCartesianMonoidalCategory.snd.{u_1, u_1 + 1}
                  (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
                  (SSet.Subcomplex.toSSet.{u_1} A))
                (SSet.Subcomplex.ι.{u_1} A)) →
            SerrePositivity.InfinityCategories.rightAnodyneExtensions.{u_1} (SSet.Subcomplex.ι.{u_1} A)
SerrePositivity.InfinityCategories.pastingCorner.{u_1} : SSet.Subcomplex.{u_1}
  (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
SerrePositivity.InfinityCategories.pastingRightSpan.{u_1} : SSet.Subcomplex.{u_1}
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1})
SerrePositivity.InfinityCategories.pastingRaiseOrderHom : OrderHom.{0, 0} (Prod.{0, 0} (Fin 2) (Fin 3)) (Fin 3)
@SerrePositivity.InfinityCategories.pastingRaiseSimplex.{u_1} : {n : Opposite.{1} SimplexCategory} →
  CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }) n →
    CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 }) n →
      CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 }) n
SerrePositivity.InfinityCategories.pastingCornerPrism.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
    (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1}))
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1})
SerrePositivity.InfinityCategories.pastingCornerPrism_zero.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (SerrePositivity.InfinityCategories.prismEndpoint.{u_1} 0
      (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1}))
    SerrePositivity.InfinityCategories.pastingCornerPrism.{u_1})
  (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1}
    (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1}))
SerrePositivity.InfinityCategories.pastingCornerRetraction.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1})
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1})
SerrePositivity.InfinityCategories.pastingCornerPrism_one.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (SerrePositivity.InfinityCategories.prismEndpoint.{u_1} 1
      (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1}))
    SerrePositivity.InfinityCategories.pastingCornerPrism.{u_1})
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.pastingCornerRetraction.{u_1}
    (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1}))
SerrePositivity.InfinityCategories.pastingRightSpan_retraction.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1})
    SerrePositivity.InfinityCategories.pastingCornerRetraction.{u_1})
  (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1}
    (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1}))
SerrePositivity.InfinityCategories.pastingCornerPrism_fixed.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (CategoryTheory.MonoidalCategoryStruct.whiskerLeft.{u_1, u_1 + 1}
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
      (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1}))
    SerrePositivity.InfinityCategories.pastingCornerPrism.{u_1})
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (CategoryTheory.SemiCartesianMonoidalCategory.snd.{u_1, u_1 + 1}
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
      (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1}))
    (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1}))
SerrePositivity.InfinityCategories.pastingRightSpan_rightAnodyne.{u_1} : SerrePositivity.InfinityCategories.rightAnodyneExtensions.{u_1}
  (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1})
@SerrePositivity.InfinityCategories.JoinCocone.restrict.{u_1} : {K₀ K X : SSet.{u_1}} →
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} →
    SerrePositivity.InfinityCategories.JoinCocone.{u_1} p →
      (f : Quiver.Hom.{u_1, u_1 + 1} K₀ K) →
        SerrePositivity.InfinityCategories.JoinCocone.{u_1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} f p)
@SerrePositivity.InfinityCategories.isColimitCone_iff_restrict_of_rightAnodyne.{u_1} : ∀ {K₀ K X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X] {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p) (f : Quiver.Hom.{u_1, u_1 + 1} K₀ K)
  [CategoryTheory.Mono.{u_1, u_1 + 1} f],
  SerrePositivity.InfinityCategories.rightAnodyneExtensions.{u_1} f →
    (SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c ↔
      SerrePositivity.InfinityCategories.IsColimitCone.{u_1}
        (SerrePositivity.InfinityCategories.JoinCocone.restrict.{u_1} c f))
@SerrePositivity.InfinityCategories.IsColimitCone.restrict_of_rightAnodyne.{u_1} : ∀ {K₀ K X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X] {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  {c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p},
  SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c →
    ∀ (f : Quiver.Hom.{u_1, u_1 + 1} K₀ K) [CategoryTheory.Mono.{u_1, u_1 + 1} f],
      SerrePositivity.InfinityCategories.rightAnodyneExtensions.{u_1} f →
        SerrePositivity.InfinityCategories.IsColimitCone.{u_1}
          (SerrePositivity.InfinityCategories.JoinCocone.restrict.{u_1} c f)
@SerrePositivity.InfinityCategories.pastingCornerRestrict_trivialKanFibration.{u_1} : ∀ {X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X]
  (p :
    Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1}) X),
  SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1}
    (SerrePositivity.InfinityCategories.sliceUnderRestrict.{u_1} p
      (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1}))
@SerrePositivity.InfinityCategories.pastingCorner_isColimitCone_iff_rightSpan.{u_1} : ∀ {X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X]
  {p :
    Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1}) X}
  (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p),
  SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c ↔
    SerrePositivity.InfinityCategories.IsColimitCone.{u_1}
      (SerrePositivity.InfinityCategories.JoinCocone.restrict.{u_1} c
        (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1}))
```

## S4：右の三頂点部分と標準 span の同定

頂点 (1,0)、(2,0)、(1,1) を 0、1、2 に符号化し、標準 span への単射を構成した。二本の辺を貼り合わせて逆射を作り、`pastingRightSpanIso : (horn 2 0 : SSet) ≅ pastingRightSpan` を証明した。
同型の長方形への包含は右四角形の span の包含に厳密に一致する。これにより、五頂点図式から標準 span への coslice の制限が trivial Kan fibration であることと、任意の余錐の余極限性をその制限で判定できることを証明した。値域の図式の比較では Quasicategory のみを仮定し、形状の同型自体には値域を仮定しない。
未完了：長方形全体の join 表示、左四角形の押し出し性を使う外側図式との比較、引き戻しへの双対化、三角構造・S5〜S7。貼り合わせ定理全体の完了とは数えない。
検証：PastingRightSpanComparison 対象ビルド 1936 jobs・Stable 集約ビルド 2009 jobs 成功。全 683 宣言／65 モジュールの公理監査成功（標準三公理のみ）。

```lean
SerrePositivity.InfinityCategories.pastingSpanCode : OrderHom.{0, 0} (Prod.{0, 0} (Fin 3) (Fin 2)) (Fin 3)
SerrePositivity.InfinityCategories.pastingSpanCodeMap.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
  (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
@SerrePositivity.InfinityCategories.pastingRightSpan_code_mem_horn.{u_1} : ∀ {n : ℕ}
  (s :
    CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
      (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1})
      (Opposite.op.{1} { len := n })),
  Membership.mem.{u_1, u_1}
    (CategoryTheory.Subfunctor.obj.{u_1, 0, 0} (SSet.horn.{u_1} 2 0) (Opposite.op.{1} { len := n }))
    ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
        (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1} SerrePositivity.InfinityCategories.pastingSpanCodeMap.{u_1}
          (Opposite.op.{1} { len := n })))
      ↑↑s)
SerrePositivity.InfinityCategories.pastingRightSpanToHorn.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1})
  (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 0))
SerrePositivity.InfinityCategories.pastingRightSpanToHorn_mono.{u_1} : CategoryTheory.Mono.{u_1, u_1 + 1}
  SerrePositivity.InfinityCategories.pastingRightSpanToHorn.{u_1}
SerrePositivity.InfinityCategories.pastingRightSpanBottom.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1})
SerrePositivity.InfinityCategories.pastingRightSpanVertical.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1})
SerrePositivity.InfinityCategories.pastingRightSpanBottom_ι.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.pastingRightSpanBottom.{u_1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1})
      (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1})))
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.squareBottomEdge.{u_1}
    (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_1 + 1}
      (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} 0)
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })))
SerrePositivity.InfinityCategories.pastingRightSpanVertical_ι.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.pastingRightSpanVertical.{u_1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1})
      (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1})))
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.squareLeftEdge.{u_1}
    (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_1 + 1}
      (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} 0)
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })))
SerrePositivity.InfinityCategories.pastingRightSpanEdges_source.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} 1)
    SerrePositivity.InfinityCategories.pastingRightSpanBottom.{u_1})
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} 1)
    SerrePositivity.InfinityCategories.pastingRightSpanVertical.{u_1})
SerrePositivity.InfinityCategories.pastingRightSpanFromHorn.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 0))
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1})
SerrePositivity.InfinityCategories.pastingRightSpanFromHorn_left.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SSet.horn₂₀.ι₀₁.{u_1}
    SerrePositivity.InfinityCategories.pastingRightSpanFromHorn.{u_1})
  SerrePositivity.InfinityCategories.pastingRightSpanBottom.{u_1}
SerrePositivity.InfinityCategories.pastingRightSpanFromHorn_right.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SSet.horn₂₀.ι₀₂.{u_1}
    SerrePositivity.InfinityCategories.pastingRightSpanFromHorn.{u_1})
  SerrePositivity.InfinityCategories.pastingRightSpanVertical.{u_1}
SerrePositivity.InfinityCategories.pastingRightSpanToHorn_ι.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.pastingRightSpanToHorn.{u_1}
    (SSet.Subcomplex.ι.{u_1} (SSet.horn.{u_1} 2 0)))
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1})
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1})
      SerrePositivity.InfinityCategories.pastingSpanCodeMap.{u_1}))
SerrePositivity.InfinityCategories.pastingRightSpanIso.{u_1} : CategoryTheory.Iso.{u_1, u_1 + 1}
  (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 0))
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1})
SerrePositivity.InfinityCategories.pastingRightSpanIso_hom_ι.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (CategoryTheory.Iso.hom.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.pastingRightSpanIso.{u_1})
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1})
      (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1})))
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.spanSquareBoundary.{u_1}
    (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_1 + 1}
      (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} 0)
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })))
@SerrePositivity.InfinityCategories.pastingCornerRestrict_standardSpan_trivialKanFibration.{u_1} : ∀ {X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X]
  (p :
    Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1}) X),
  SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1}
    (SerrePositivity.InfinityCategories.sliceUnderRestrict.{u_1} p
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (CategoryTheory.Iso.hom.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.pastingRightSpanIso.{u_1})
        (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1})))
@SerrePositivity.InfinityCategories.pastingCorner_isColimitCone_iff_standardSpan.{u_1} : ∀ {X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X]
  {p :
    Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1}) X}
  (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p),
  SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c ↔
    SerrePositivity.InfinityCategories.IsColimitCone.{u_1}
      (SerrePositivity.InfinityCategories.JoinCocone.restrict.{u_1} c
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
          (CategoryTheory.Iso.hom.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.pastingRightSpanIso.{u_1})
          (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1})))
```


## S4：長方形の終端角による join 表示

対象 `PastingCornerJoinIso`（1921 jobs）・集約 `Stable`（2012 jobs）のビルドは成功。
全宣言監査は 68 モジュール・720 宣言で標準三公理のみ。
右四角形の余錐との厳密な一致、左四角形の押し出し性を使う外側比較、
貼り合わせ全体・三角構造・S5〜S7 は未完了。

以下は `pp.universes true` での公開宣言の正確な型。

```lean
SerrePositivity.InfinityCategories.stableLastCollapseOrderHom : (n : ℕ) →
  OrderHom.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} n 2)) (Fin (HAdd.hAdd.{0, 0, 0} n 1))
SerrePositivity.InfinityCategories.stableLastJoinEvaluation.{u_1} : (n : ℕ) →
  Quiver.Hom.{u_1, u_1 + 1}
    (SerrePositivity.InfinityCategories.join.{u_1}
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := n })
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := n })
SerrePositivity.InfinityCategories.stableLastJoinEvaluation_app_val.{u_1} : ∀ (n d : ℕ)
  (s :
    SerrePositivity.InfinityCategories.Join.Simplex.{u_1}
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := n })
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }) d)
  (i : Fin (HAdd.hAdd.{0, 0, 0} d 1)),
  Eq.{1}
    (↑(((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
            (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
              (SerrePositivity.InfinityCategories.stableLastJoinEvaluation.{u_1} n) (Opposite.op.{1} { len := d })))
          s)
        i))
    (min.{0} (↑((SerrePositivity.InfinityCategories.Join.stdEncode.{u_1} n 0 d s) i)) n)
SerrePositivity.InfinityCategories.stableLastJoinEvaluation_app_of_lt.{u_1} : ∀ (n d : ℕ)
  (s :
    SerrePositivity.InfinityCategories.Join.Simplex.{u_1}
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := n })
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }) d)
  (i : Fin (HAdd.hAdd.{0, 0, 0} d 1)) (hi : LT.lt.{0} ↑i ↑(Sigma.fst.{0, u_1} s)),
  Eq.{1}
    (((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
          (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
            (SerrePositivity.InfinityCategories.stableLastJoinEvaluation.{u_1} n) (Opposite.op.{1} { len := d })))
        s)
      i)
    (((SerrePositivity.InfinityCategories.Join.stdAugEquiv.{u_1} n ↑(Sigma.fst.{0, u_1} s)) (Sigma.snd.{0, u_1} s).1)
      ⟨↑i, hi⟩)
SerrePositivity.InfinityCategories.stableLastJoinEvaluation_app_of_ge.{u_1} : ∀ (n d : ℕ)
  (s :
    SerrePositivity.InfinityCategories.Join.Simplex.{u_1}
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := n })
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }) d)
  (i : Fin (HAdd.hAdd.{0, 0, 0} d 1)),
  LE.le.{0} ↑(Sigma.fst.{0, u_1} s) ↑i →
    Eq.{1}
      (((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
            (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
              (SerrePositivity.InfinityCategories.stableLastJoinEvaluation.{u_1} n) (Opposite.op.{1} { len := d })))
          s)
        i)
      (Fin.last n)
SerrePositivity.InfinityCategories.stableLastJoinEvaluation_inl.{u_1} : ∀ (n : ℕ),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.joinInl.{u_1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := n })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
      (SerrePositivity.InfinityCategories.stableLastJoinEvaluation.{u_1} n))
    (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1}
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := n }))
SerrePositivity.InfinityCategories.pastingAugX.{u_1} : (ℓ : ℕ) →
  SerrePositivity.InfinityCategories.Join.augObj.{u_1}
      (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1}) ℓ →
    OrderHom.{0, 0} (Fin ℓ) (Fin 3)
SerrePositivity.InfinityCategories.pastingAugY.{u_1} : (ℓ : ℕ) →
  SerrePositivity.InfinityCategories.Join.augObj.{u_1}
      (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1}) ℓ →
    OrderHom.{0, 0} (Fin ℓ) (Fin 2)
SerrePositivity.InfinityCategories.pastingAug_not_terminal.{u_1} : ∀ (ℓ : ℕ)
  (s :
    SerrePositivity.InfinityCategories.Join.augObj.{u_1}
      (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1}) ℓ)
  (i : Fin ℓ),
  Eq.{1} ((SerrePositivity.InfinityCategories.pastingAugX.{u_1} ℓ s) i) 2 →
    Ne.{1} ((SerrePositivity.InfinityCategories.pastingAugY.{u_1} ℓ s) i) 1
SerrePositivity.InfinityCategories.pastingCornerCocone.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (SerrePositivity.InfinityCategories.join.{u_1}
    (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1})
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
  (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
SerrePositivity.InfinityCategories.pastingCornerCocone_inl.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (SerrePositivity.InfinityCategories.joinInl.{u_1}
      (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1})
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
    SerrePositivity.InfinityCategories.pastingCornerCocone.{u_1})
  (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1})
@SerrePositivity.InfinityCategories.pastingCornerCocone_appX_of_lt.{u_1} : ∀ {d : ℕ}
  (s :
    SerrePositivity.InfinityCategories.Join.Simplex.{u_1}
      (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1})
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }) d)
  (i : Fin (HAdd.hAdd.{0, 0, 0} d 1)) (hi : LT.lt.{0} ↑i ↑(Sigma.fst.{0, u_1} s)),
  Eq.{1}
    (((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
            (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
              SerrePositivity.InfinityCategories.pastingCornerCocone.{u_1} (Opposite.op.{1} { len := d })))
          s).1
      i)
    ((SerrePositivity.InfinityCategories.pastingAugX.{u_1} (↑(Sigma.fst.{0, u_1} s)) (Sigma.snd.{0, u_1} s).1) ⟨↑i, hi⟩)
@SerrePositivity.InfinityCategories.pastingCornerCocone_appY_of_lt.{u_1} : ∀ {d : ℕ}
  (s :
    SerrePositivity.InfinityCategories.Join.Simplex.{u_1}
      (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1})
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }) d)
  (i : Fin (HAdd.hAdd.{0, 0, 0} d 1)) (hi : LT.lt.{0} ↑i ↑(Sigma.fst.{0, u_1} s)),
  Eq.{1}
    (((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
            (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
              SerrePositivity.InfinityCategories.pastingCornerCocone.{u_1} (Opposite.op.{1} { len := d })))
          s).2
      i)
    ((SerrePositivity.InfinityCategories.pastingAugY.{u_1} (↑(Sigma.fst.{0, u_1} s)) (Sigma.snd.{0, u_1} s).1) ⟨↑i, hi⟩)
@SerrePositivity.InfinityCategories.pastingCornerCocone_app_of_ge.{u_1} : ∀ {d : ℕ}
  (s :
    SerrePositivity.InfinityCategories.Join.Simplex.{u_1}
      (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1})
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }) d)
  (i : Fin (HAdd.hAdd.{0, 0, 0} d 1)),
  LE.le.{0} ↑(Sigma.fst.{0, u_1} s) ↑i →
    Eq.{1}
        (((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
                (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
                  SerrePositivity.InfinityCategories.pastingCornerCocone.{u_1} (Opposite.op.{1} { len := d })))
              s).1
          i)
        2 ∧
      Eq.{1}
        (((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
                (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
                  SerrePositivity.InfinityCategories.pastingCornerCocone.{u_1} (Opposite.op.{1} { len := d })))
              s).2
          i)
        1
@SerrePositivity.InfinityCategories.pastingCornerCocone_vertex_corner_iff.{u_1} : ∀ {d : ℕ}
  (s :
    SerrePositivity.InfinityCategories.Join.Simplex.{u_1}
      (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1})
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }) d)
  (i : Fin (HAdd.hAdd.{0, 0, 0} d 1)),
  Eq.{1}
        (((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
                (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
                  SerrePositivity.InfinityCategories.pastingCornerCocone.{u_1} (Opposite.op.{1} { len := d })))
              s).1
          i)
        2 →
      Ne.{1}
        (((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
                (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1}
                  SerrePositivity.InfinityCategories.pastingCornerCocone.{u_1} (Opposite.op.{1} { len := d })))
              s).2
          i)
        1 ↔
    LT.lt.{0} ↑i ↑(Sigma.fst.{0, u_1} s)
SerrePositivity.InfinityCategories.pastingCornerCocone_app_injective.{u_1} : ∀ (d : ℕ),
  Function.Injective.{u_1 + 1, u_1 + 1}
    ⇑(CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
        (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1} SerrePositivity.InfinityCategories.pastingCornerCocone.{u_1}
          (Opposite.op.{1} { len := d })))
SerrePositivity.InfinityCategories.pastingTerminalFlag : OrderHom.{0, 0} (Prod.{0, 0} (Fin 3) (Fin 2)) (Fin 2)
SerrePositivity.InfinityCategories.pastingTerminalFlag_lt : ∀ (x : Fin 3) (y : Fin 2),
  LT.lt.{0} (↑(SerrePositivity.InfinityCategories.pastingTerminalFlag (Prod.mk.{0, 0} x y))) 1 ↔ Eq.{1} x 2 → Ne.{1} y 1
SerrePositivity.InfinityCategories.pastingAugOfCoords.{u_1} : (r : ℕ) →
  (x : OrderHom.{0, 0} (Fin r) (Fin 3)) →
    (y : OrderHom.{0, 0} (Fin r) (Fin 2)) →
      (∀ (i : Fin r), Eq.{1} (x i) 2 → Ne.{1} (y i) 1) →
        SerrePositivity.InfinityCategories.Join.augObj.{u_1}
          (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1}) r
SerrePositivity.InfinityCategories.pastingAugOfCoords_x.{u_1} : ∀ (r : ℕ) (x : OrderHom.{0, 0} (Fin r) (Fin 3))
  (y : OrderHom.{0, 0} (Fin r) (Fin 2)) (h : ∀ (i : Fin r), Eq.{1} (x i) 2 → Ne.{1} (y i) 1) (i : Fin r),
  Eq.{1}
    ((SerrePositivity.InfinityCategories.pastingAugX.{u_1} r
        (SerrePositivity.InfinityCategories.pastingAugOfCoords.{u_1} r x y h))
      i)
    (x i)
SerrePositivity.InfinityCategories.pastingAugOfCoords_y.{u_1} : ∀ (r : ℕ) (x : OrderHom.{0, 0} (Fin r) (Fin 3))
  (y : OrderHom.{0, 0} (Fin r) (Fin 2)) (h : ∀ (i : Fin r), Eq.{1} (x i) 2 → Ne.{1} (y i) 1) (i : Fin r),
  Eq.{1}
    ((SerrePositivity.InfinityCategories.pastingAugY.{u_1} r
        (SerrePositivity.InfinityCategories.pastingAugOfCoords.{u_1} r x y h))
      i)
    (y i)
SerrePositivity.InfinityCategories.pastingCornerCocone_app_surjective.{u_1} : ∀ (d : ℕ),
  Function.Surjective.{u_1 + 1, u_1 + 1}
    ⇑(CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
        (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1} SerrePositivity.InfinityCategories.pastingCornerCocone.{u_1}
          (Opposite.op.{1} { len := d })))
SerrePositivity.InfinityCategories.pastingCornerCocone_isIso.{u_1} : CategoryTheory.IsIso.{u_1, u_1 + 1}
  SerrePositivity.InfinityCategories.pastingCornerCocone.{u_1}
SerrePositivity.InfinityCategories.pastingCornerJoinIso.{u_1} : CategoryTheory.Iso.{u_1, u_1 + 1}
  (SerrePositivity.InfinityCategories.join.{u_1}
    (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1})
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
  (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
```


## S4：長方形の余錐と右四角形の比較

対象 `PastingRightCocone` と集約 `Stable` のビルドは成功（2013 jobs）。
全宣言監査は 69 モジュール・727 宣言で標準三公理のみ。
左四角形の押し出し性を使う外側比較、貼り合わせ全体・三角構造・S5〜S7 は未完了。

```lean
@SerrePositivity.InfinityCategories.stableJoin_prodStdSimplex_hom_ext.{u_1} : ∀ {K L : SSet.{u_1}} {m n : ℕ}
  {f g :
    Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.join.{u_1} K L)
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := m })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := n }))},
  Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.joinInl.{u_1} K L) f)
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.joinInl.{u_1} K L) g) →
    Eq.{u_1 + 1}
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.joinInr.{u_1} K L) f)
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.joinInr.{u_1} K L) g) →
      Eq.{u_1 + 1} f g
SerrePositivity.InfinityCategories.pastingCornerCocone_rightSpan.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (SerrePositivity.InfinityCategories.joinMap.{u_1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (CategoryTheory.Iso.hom.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.pastingRightSpanIso.{u_1})
        (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1}))
      (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 })))
    SerrePositivity.InfinityCategories.pastingCornerCocone.{u_1})
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (CategoryTheory.Iso.hom.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.spanCoconeSquareIso.{u_1})
    (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_1 + 1}
      (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} 0)
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })))
@SerrePositivity.InfinityCategories.isColimitCone_iff_of_val_eq.{u_1} : ∀ {K X : SSet.{u_1}}
  {p q : Quiver.Hom.{u_1, u_1 + 1} K X} (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p)
  (d : SerrePositivity.InfinityCategories.JoinCocone.{u_1} q),
  Eq.{u_1 + 1} ↑c ↑d →
    (SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c ↔
      SerrePositivity.InfinityCategories.IsColimitCone.{u_1} d)
@SerrePositivity.InfinityCategories.pastingCocone.{u_1} : {X : SSet.{u_1}} →
  (F :
      Quiver.Hom.{u_1, u_1 + 1}
        (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
        X) →
    SerrePositivity.InfinityCategories.JoinCocone.{u_1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1}) F)
@SerrePositivity.InfinityCategories.pastingCocone_isColimitCone_iff_right.{u_1} : ∀ {X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X]
  (F :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X),
  SerrePositivity.InfinityCategories.IsColimitCone.{u_1} (SerrePositivity.InfinityCategories.pastingCocone.{u_1} F) ↔
    SerrePositivity.InfinityCategories.IsPushoutSquare.{u_1}
      (SerrePositivity.InfinityCategories.pastingSquare.{u_1} F 0)
```


## S4：四頂点図式、外側 span、外側四角形の余錐

対象 `PastingOuterCocone` と集約 `Stable` のビルドは成功（2016 jobs）。
全宣言監査は 72 モジュール・782 宣言で標準三公理のみ。
外側 span への right anodyne な制限、標準ホーンとの同型、形状の厳密な一致、
四頂点図式上の余極限性と外側四角形の押し出し性の同値を証明した。
左四角形が押し出しの場合の五頂点余錐と四頂点余錐の余極限性の比較は未証明。
従って貼り合わせ全体・双対化・三角構造・S5〜S7 は未完了。

```lean
SerrePositivity.InfinityCategories.pastingOuterBase.{u_1} : SSet.Subcomplex.{u_1}
  (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
SerrePositivity.InfinityCategories.pastingOuterSpan.{u_1} : SSet.Subcomplex.{u_1}
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingOuterBase.{u_1})
SerrePositivity.InfinityCategories.pastingOuterRaiseOrderHom : OrderHom.{0, 0} (Prod.{0, 0} (Fin 2) (Fin 3)) (Fin 3)
@SerrePositivity.InfinityCategories.pastingOuterRaiseSimplex.{u_1} : {n : Opposite.{1} SimplexCategory} →
  CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }) n →
    CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 }) n →
      CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 }) n
SerrePositivity.InfinityCategories.pastingOuterBasePrism.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
    (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingOuterBase.{u_1}))
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingOuterBase.{u_1})
SerrePositivity.InfinityCategories.pastingOuterBasePrism_zero.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (SerrePositivity.InfinityCategories.prismEndpoint.{u_1} 0
      (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingOuterBase.{u_1}))
    SerrePositivity.InfinityCategories.pastingOuterBasePrism.{u_1})
  (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1}
    (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingOuterBase.{u_1}))
SerrePositivity.InfinityCategories.pastingOuterBaseRetraction.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingOuterBase.{u_1})
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingOuterSpan.{u_1})
SerrePositivity.InfinityCategories.pastingOuterBasePrism_one.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (SerrePositivity.InfinityCategories.prismEndpoint.{u_1} 1
      (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingOuterBase.{u_1}))
    SerrePositivity.InfinityCategories.pastingOuterBasePrism.{u_1})
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.pastingOuterBaseRetraction.{u_1}
    (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingOuterSpan.{u_1}))
SerrePositivity.InfinityCategories.pastingOuterSpan_retraction.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingOuterSpan.{u_1})
    SerrePositivity.InfinityCategories.pastingOuterBaseRetraction.{u_1})
  (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1}
    (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingOuterSpan.{u_1}))
SerrePositivity.InfinityCategories.pastingOuterBasePrism_fixed.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (CategoryTheory.MonoidalCategoryStruct.whiskerLeft.{u_1, u_1 + 1}
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
      (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingOuterSpan.{u_1}))
    SerrePositivity.InfinityCategories.pastingOuterBasePrism.{u_1})
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (CategoryTheory.SemiCartesianMonoidalCategory.snd.{u_1, u_1 + 1}
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
      (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingOuterSpan.{u_1}))
    (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingOuterSpan.{u_1}))
SerrePositivity.InfinityCategories.pastingOuterSpan_rightAnodyne.{u_1} : SerrePositivity.InfinityCategories.rightAnodyneExtensions.{u_1}
  (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingOuterSpan.{u_1})
SerrePositivity.InfinityCategories.pastingOuterBase_le_corner.{u_1} : LE.le.{u_1}
  SerrePositivity.InfinityCategories.pastingOuterBase.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1}
SerrePositivity.InfinityCategories.pastingOuterBaseToCorner.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingOuterBase.{u_1})
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1})
@SerrePositivity.InfinityCategories.pastingOuterBaseRestrict_trivialKanFibration.{u_1} : ∀ {X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X]
  (p :
    Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingOuterBase.{u_1})
      X),
  SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1}
    (SerrePositivity.InfinityCategories.sliceUnderRestrict.{u_1} p
      (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingOuterSpan.{u_1}))
@SerrePositivity.InfinityCategories.pastingOuterBase_isColimitCone_iff_outerSpan.{u_1} : ∀ {X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X]
  {p :
    Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingOuterBase.{u_1})
      X}
  (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p),
  SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c ↔
    SerrePositivity.InfinityCategories.IsColimitCone.{u_1}
      (SerrePositivity.InfinityCategories.JoinCocone.restrict.{u_1} c
        (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingOuterSpan.{u_1}))
SerrePositivity.InfinityCategories.pastingOuterLowerOrderHom : OrderHom.{0, 0} (Fin 3) (Fin 3)
@SerrePositivity.InfinityCategories.pastingOuterLowerSimplex.{u_1} : {n : Opposite.{1} SimplexCategory} →
  CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 }) n →
    CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 }) n
SerrePositivity.InfinityCategories.pastingOuterSpanToRight.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingOuterSpan.{u_1})
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1})
SerrePositivity.InfinityCategories.pastingRightSpanToOuter.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1})
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingOuterSpan.{u_1})
SerrePositivity.InfinityCategories.pastingOuterSpanRightIso.{u_1} : CategoryTheory.Iso.{u_1, u_1 + 1}
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingOuterSpan.{u_1})
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1})
SerrePositivity.InfinityCategories.pastingOuterSpanIso.{u_1} : CategoryTheory.Iso.{u_1, u_1 + 1}
  (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 0))
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingOuterSpan.{u_1})
SerrePositivity.InfinityCategories.pastingOuterSpanIso_hom_ι.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (CategoryTheory.Iso.hom.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.pastingOuterSpanIso.{u_1})
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingOuterSpan.{u_1})
      (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingOuterBase.{u_1})))
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.spanSquareBoundary.{u_1}
    (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_1 + 1}
      (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} 1)
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })))
@SerrePositivity.InfinityCategories.pastingOuterBaseRestrict_standardSpan_trivialKanFibration.{u_1} : ∀ {X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X]
  (p :
    Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingOuterBase.{u_1})
      X),
  SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1}
    (SerrePositivity.InfinityCategories.sliceUnderRestrict.{u_1} p
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (CategoryTheory.Iso.hom.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.pastingOuterSpanIso.{u_1})
        (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingOuterSpan.{u_1})))
@SerrePositivity.InfinityCategories.pastingOuterBase_isColimitCone_iff_standardSpan.{u_1} : ∀ {X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X]
  {p :
    Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingOuterBase.{u_1})
      X}
  (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p),
  SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c ↔
    SerrePositivity.InfinityCategories.IsColimitCone.{u_1}
      (SerrePositivity.InfinityCategories.JoinCocone.restrict.{u_1} c
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
          (CategoryTheory.Iso.hom.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.pastingOuterSpanIso.{u_1})
          (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingOuterSpan.{u_1})))
SerrePositivity.InfinityCategories.pastingCornerCocone_outerSpan.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (SerrePositivity.InfinityCategories.joinMap.{u_1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (CategoryTheory.Iso.hom.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.pastingOuterSpanIso.{u_1})
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
          (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingOuterSpan.{u_1})
          SerrePositivity.InfinityCategories.pastingOuterBaseToCorner.{u_1}))
      (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 })))
    SerrePositivity.InfinityCategories.pastingCornerCocone.{u_1})
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (CategoryTheory.Iso.hom.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.spanCoconeSquareIso.{u_1})
    (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_1 + 1}
      (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} 1)
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })))
@SerrePositivity.InfinityCategories.pastingOuterCocone.{u_1} : {X : SSet.{u_1}} →
  (F :
      Quiver.Hom.{u_1, u_1 + 1}
        (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
        X) →
    SerrePositivity.InfinityCategories.JoinCocone.{u_1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        SerrePositivity.InfinityCategories.pastingOuterBaseToCorner.{u_1}
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
          (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1}) F))
@SerrePositivity.InfinityCategories.pastingOuterCocone_isColimitCone_iff_outer.{u_1} : ∀ {X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X]
  (F :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X),
  SerrePositivity.InfinityCategories.IsColimitCone.{u_1}
      (SerrePositivity.InfinityCategories.pastingOuterCocone.{u_1} F) ↔
    SerrePositivity.InfinityCategories.IsPushoutSquare.{u_1}
      (SerrePositivity.InfinityCategories.pastingSquare.{u_1} F 1)
```


## S4：二重 coslice のための補った join と切断の組み替え

対象 `JoinCutCalculus` と集約 `Stable` のビルドは成功（2019 jobs）。
全宣言監査は 75 モジュール・831 宣言で標準三公理のみ。
空次数を含む join の切断表示の自然性、三因子の各次数の同値、
左右の区間および中間区間の切断の引き戻しの公式を証明した。
三因子の組み替えの自然性全体・単体集合としての結合同型・二重 coslice への適用は未完了。
左押し出しによる五頂点／四頂点余錐の比較、貼り合わせ本体、三角構造・S5〜S7 も未完了。

```lean
SerrePositivity.InfinityCategories.StableAugJoin.{u_1} : SSet.{u_1} → SSet.{u_1} → ℕ → Type u_1
SerrePositivity.InfinityCategories.stableAugJoin_zero_subsingleton.{u_1} : ∀ (K L : SSet.{u_1}),
  Subsingleton.{u_1 + 1} (SerrePositivity.InfinityCategories.StableAugJoin.{u_1} K L 0)
SerrePositivity.InfinityCategories.stableAugJoinEquiv.{u_1} : (K L : SSet.{u_1}) →
  (r : ℕ) →
    Equiv.{u_1 + 1, u_1 + 1}
      (SerrePositivity.InfinityCategories.Join.augObj.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) r)
      (SerrePositivity.InfinityCategories.StableAugJoin.{u_1} K L r)
SerrePositivity.InfinityCategories.stableAugJoinMap.{u_1} : (K L : SSet.{u_1}) →
  {r s : ℕ} →
    OrderHom.{0, 0} (Fin r) (Fin s) →
      SerrePositivity.InfinityCategories.StableAugJoin.{u_1} K L s →
        SerrePositivity.InfinityCategories.StableAugJoin.{u_1} K L r
SerrePositivity.InfinityCategories.stableAugJoinEquiv_naturality.{u_1} : ∀ (K L : SSet.{u_1}) {r s : ℕ}
  (α : OrderHom.{0, 0} (Fin r) (Fin s))
  (x : SerrePositivity.InfinityCategories.Join.augObj.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) s),
  Eq.{u_1 + 1}
    ((SerrePositivity.InfinityCategories.stableAugJoinEquiv.{u_1} K L r)
      (SerrePositivity.InfinityCategories.Join.augMap.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) α x))
    (SerrePositivity.InfinityCategories.stableAugJoinMap.{u_1} K L α
      ((SerrePositivity.InfinityCategories.stableAugJoinEquiv.{u_1} K L s) x))
@SerrePositivity.InfinityCategories.stableAugJoin_ext.{u_1} : ∀ {K L : SSet.{u_1}} {r : ℕ}
  (s t : SerrePositivity.InfinityCategories.StableAugJoin.{u_1} K L r)
  (hc : Eq.{1} (Sigma.fst.{0, u_1} s) (Sigma.fst.{0, u_1} t)),
  Eq.{u_1 + 1} (cast.{u_1 + 1} ⋯ (Sigma.snd.{0, u_1} s).1) (Sigma.snd.{0, u_1} t).1 →
    Eq.{u_1 + 1} (cast.{u_1 + 1} ⋯ (Sigma.snd.{0, u_1} s).2) (Sigma.snd.{0, u_1} t).2 → Eq.{u_1 + 1} s t
SerrePositivity.InfinityCategories.stableJoinCutEquiv : (r : ℕ) →
  Equiv.{1, 1} ((b : Fin (HAdd.hAdd.{0, 0, 0} r 1)) × Fin (HAdd.hAdd.{0, 0, 0} (↑b) 1))
    ((a : Fin (HAdd.hAdd.{0, 0, 0} r 1)) × Fin (HAdd.hAdd.{0, 0, 0} (HSub.hSub.{0, 0, 0} r ↑a) 1))
SerrePositivity.InfinityCategories.stableProdSigmaEquiv.{u_1, u_2,
  u_3} : (A : Type u_1) →
  (I : Type u_2) →
    (B : I → Type u_3) →
      Equiv.{max ((max u_3 u_2) + 1) (u_1 + 1), max ((max u_3 u_1) + 1) (u_2 + 1)}
        (Prod.{u_1, max u_3 u_2} A ((i : I) × B i)) ((i : I) × Prod.{u_1, u_3} A (B i))
SerrePositivity.InfinityCategories.stableAugJoinLeftTripleEquiv.{u_1} : (K L M : SSet.{u_1}) →
  (r : ℕ) →
    Equiv.{u_1 + 1, u_1 + 1}
      (SerrePositivity.InfinityCategories.StableAugJoin.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) M r)
      ((s : (b : Fin (HAdd.hAdd.{0, 0, 0} r 1)) × Fin (HAdd.hAdd.{0, 0, 0} (↑b) 1)) ×
        Prod.{u_1, u_1}
          (Prod.{u_1, u_1} (SerrePositivity.InfinityCategories.Join.augObj.{u_1} K ↑(Sigma.snd.{0, 0} s))
            (SerrePositivity.InfinityCategories.Join.augObj.{u_1} L
              (HSub.hSub.{0, 0, 0} ↑(Sigma.fst.{0, 0} s) ↑(Sigma.snd.{0, 0} s))))
          (SerrePositivity.InfinityCategories.Join.augObj.{u_1} M (HSub.hSub.{0, 0, 0} r ↑(Sigma.fst.{0, 0} s))))
SerrePositivity.InfinityCategories.stableAugJoinRightTripleEquiv.{u_1} : (K L M : SSet.{u_1}) →
  (r : ℕ) →
    Equiv.{u_1 + 1, u_1 + 1}
      (SerrePositivity.InfinityCategories.StableAugJoin.{u_1} K (SerrePositivity.InfinityCategories.join.{u_1} L M) r)
      ((s : (a : Fin (HAdd.hAdd.{0, 0, 0} r 1)) × Fin (HAdd.hAdd.{0, 0, 0} (HSub.hSub.{0, 0, 0} r ↑a) 1)) ×
        Prod.{u_1, u_1} (SerrePositivity.InfinityCategories.Join.augObj.{u_1} K ↑(Sigma.fst.{0, 0} s))
          (Prod.{u_1, u_1} (SerrePositivity.InfinityCategories.Join.augObj.{u_1} L ↑(Sigma.snd.{0, 0} s))
            (SerrePositivity.InfinityCategories.Join.augObj.{u_1} M
              (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} r ↑(Sigma.fst.{0, 0} s)) ↑(Sigma.snd.{0, 0} s)))))
SerrePositivity.InfinityCategories.stableJoinCutFiberEquiv.{u_1} : (K L M : SSet.{u_1}) →
  (r : ℕ) →
    (s : (b : Fin (HAdd.hAdd.{0, 0, 0} r 1)) × Fin (HAdd.hAdd.{0, 0, 0} (↑b) 1)) →
      Equiv.{u_1 + 1, u_1 + 1}
        (Prod.{u_1, u_1}
          (Prod.{u_1, u_1} (SerrePositivity.InfinityCategories.Join.augObj.{u_1} K ↑(Sigma.snd.{0, 0} s))
            (SerrePositivity.InfinityCategories.Join.augObj.{u_1} L
              (HSub.hSub.{0, 0, 0} ↑(Sigma.fst.{0, 0} s) ↑(Sigma.snd.{0, 0} s))))
          (SerrePositivity.InfinityCategories.Join.augObj.{u_1} M (HSub.hSub.{0, 0, 0} r ↑(Sigma.fst.{0, 0} s))))
        (Prod.{u_1, u_1}
          (SerrePositivity.InfinityCategories.Join.augObj.{u_1} K
            ↑(Sigma.fst.{0, 0} ((SerrePositivity.InfinityCategories.stableJoinCutEquiv r) s)))
          (Prod.{u_1, u_1}
            (SerrePositivity.InfinityCategories.Join.augObj.{u_1} L
              ↑(Sigma.snd.{0, 0} ((SerrePositivity.InfinityCategories.stableJoinCutEquiv r) s)))
            (SerrePositivity.InfinityCategories.Join.augObj.{u_1} M
              (HSub.hSub.{0, 0, 0}
                (HSub.hSub.{0, 0, 0} r
                  ↑(Sigma.fst.{0, 0} ((SerrePositivity.InfinityCategories.stableJoinCutEquiv r) s)))
                ↑(Sigma.snd.{0, 0} ((SerrePositivity.InfinityCategories.stableJoinCutEquiv r) s))))))
SerrePositivity.InfinityCategories.stableAugReassociationEquiv.{u_1} : (K L M : SSet.{u_1}) →
  (r : ℕ) →
    Equiv.{u_1 + 1, u_1 + 1}
      (SerrePositivity.InfinityCategories.StableAugJoin.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) M r)
      (SerrePositivity.InfinityCategories.StableAugJoin.{u_1} K (SerrePositivity.InfinityCategories.join.{u_1} L M) r)
SerrePositivity.InfinityCategories.stableAugJoinAssociatorEquiv.{u_1} : (K L M : SSet.{u_1}) →
  (r : ℕ) →
    Equiv.{u_1 + 1, u_1 + 1}
      (SerrePositivity.InfinityCategories.Join.augObj.{u_1}
        (SerrePositivity.InfinityCategories.join.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) M) r)
      (SerrePositivity.InfinityCategories.Join.augObj.{u_1}
        (SerrePositivity.InfinityCategories.join.{u_1} K (SerrePositivity.InfinityCategories.join.{u_1} L M)) r)
@SerrePositivity.InfinityCategories.stablePullCut_mono : ∀ {m n : ℕ} (α : OrderHom.{0, 0} (Fin m) (Fin n)) {a b : ℕ},
  LE.le.{0} a b →
    LE.le.{0} (SerrePositivity.InfinityCategories.Join.pullCut α a)
      (SerrePositivity.InfinityCategories.Join.pullCut α b)
@SerrePositivity.InfinityCategories.stablePullCut_leftMap : ∀ {m n : ℕ} (α : OrderHom.{0, 0} (Fin m) (Fin n)) {a b : ℕ},
  LE.le.{0} a b →
    Eq.{1} (SerrePositivity.InfinityCategories.Join.pullCut (SerrePositivity.InfinityCategories.Join.leftMap α b) a)
      (SerrePositivity.InfinityCategories.Join.pullCut α a)
@SerrePositivity.InfinityCategories.stablePullCut_rightMap : ∀ {m n : ℕ} (α : OrderHom.{0, 0} (Fin m) (Fin n))
  (a b : ℕ),
  Eq.{1} (SerrePositivity.InfinityCategories.Join.pullCut (SerrePositivity.InfinityCategories.Join.rightMap α a) b)
    (HSub.hSub.{0, 0, 0} (SerrePositivity.InfinityCategories.Join.pullCut α (HAdd.hAdd.{0, 0, 0} a b))
      (SerrePositivity.InfinityCategories.Join.pullCut α a))
@SerrePositivity.InfinityCategories.stablePullCut_middle : ∀ {m n : ℕ} (α : OrderHom.{0, 0} (Fin m) (Fin n)) {a b : ℕ},
  LE.le.{0} a b →
    Eq.{1}
      (SerrePositivity.InfinityCategories.Join.pullCut (SerrePositivity.InfinityCategories.Join.rightMap α a)
        (HSub.hSub.{0, 0, 0} b a))
      (HSub.hSub.{0, 0, 0} (SerrePositivity.InfinityCategories.Join.pullCut α b)
        (SerrePositivity.InfinityCategories.Join.pullCut α a))
```


## S4：join の結合同型、因子に関する自然性、包含との両立

対象 `JoinAssociatorBoundary` と集約 `Stable` のビルドは成功（2023 jobs）。
全宣言監査は 79 モジュール・877 宣言で標準三公理のみ。
空次数を含む任意の順序写像と三つの因子の射について組み替えの自然性を証明し、
単体集合としての結合同型と左右の包含との厳密な可換性を構成した。
二重 coslice への適用、左押し出しによる五頂点／四頂点余錐の比較、
貼り合わせ本体・三角構造・S5〜S7 は未完了。

```lean
SerrePositivity.InfinityCategories.stableAugReassociation_cut.{u_1} : ∀ (K L M : SSet.{u_1}) (r : ℕ)
  (s : SerrePositivity.InfinityCategories.StableAugJoin.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) M r),
  Eq.{1} ↑(Sigma.fst.{0, u_1} ((SerrePositivity.InfinityCategories.stableAugReassociationEquiv.{u_1} K L M r) s))
    ↑(Sigma.fst.{0, u_1}
        ((SerrePositivity.InfinityCategories.stableAugJoinEquiv.{u_1} K L ↑(Sigma.fst.{0, u_1} s))
          (Sigma.snd.{0, u_1} s).1))
SerrePositivity.InfinityCategories.stableAugReassociation_decode.{u_1} : ∀ (K L M : SSet.{u_1}) (r : ℕ)
  (s : SerrePositivity.InfinityCategories.StableAugJoin.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) M r),
  Eq.{u_1 + 1}
    ((SerrePositivity.InfinityCategories.stableAugJoinRightTripleEquiv.{u_1} K L M r)
      ((SerrePositivity.InfinityCategories.stableAugReassociationEquiv.{u_1} K L M r) s))
    ((Equiv.sigmaCongr.{0, 0, u_1, u_1} (SerrePositivity.InfinityCategories.stableJoinCutEquiv r)
        (SerrePositivity.InfinityCategories.stableJoinCutFiberEquiv.{u_1} K L M r))
      ((SerrePositivity.InfinityCategories.stableAugJoinLeftTripleEquiv.{u_1} K L M r) s))
@SerrePositivity.InfinityCategories.stableAugJoin_hext.{u_1} : ∀ {K L : SSet.{u_1}} {r : ℕ}
  (s t : SerrePositivity.InfinityCategories.StableAugJoin.{u_1} K L r),
  Eq.{1} ↑(Sigma.fst.{0, u_1} s) ↑(Sigma.fst.{0, u_1} t) →
    HEq.{u_1 + 1} (Sigma.snd.{0, u_1} s).1 (Sigma.snd.{0, u_1} t).1 →
      HEq.{u_1 + 1} (Sigma.snd.{0, u_1} s).2 (Sigma.snd.{0, u_1} t).2 → Eq.{u_1 + 1} s t
@SerrePositivity.InfinityCategories.stableAugJoin_left_heq.{u_1} : ∀ {K L : SSet.{u_1}} {r : ℕ}
  {s t : SerrePositivity.InfinityCategories.StableAugJoin.{u_1} K L r},
  Eq.{u_1 + 1} s t → HEq.{u_1 + 1} (Sigma.snd.{0, u_1} s).1 (Sigma.snd.{0, u_1} t).1
@SerrePositivity.InfinityCategories.stableAugJoin_right_heq.{u_1} : ∀ {K L : SSet.{u_1}} {r : ℕ}
  {s t : SerrePositivity.InfinityCategories.StableAugJoin.{u_1} K L r},
  Eq.{u_1 + 1} s t → HEq.{u_1 + 1} (Sigma.snd.{0, u_1} s).2 (Sigma.snd.{0, u_1} t).2
@SerrePositivity.InfinityCategories.stableAugJoin_hext_total.{u_1} : ∀ {K L : SSet.{u_1}} {r r' : ℕ},
  Eq.{1} r r' →
    ∀ (s : SerrePositivity.InfinityCategories.StableAugJoin.{u_1} K L r)
      (t : SerrePositivity.InfinityCategories.StableAugJoin.{u_1} K L r'),
      Eq.{1} ↑(Sigma.fst.{0, u_1} s) ↑(Sigma.fst.{0, u_1} t) →
        HEq.{u_1 + 1} (Sigma.snd.{0, u_1} s).1 (Sigma.snd.{0, u_1} t).1 →
          HEq.{u_1 + 1} (Sigma.snd.{0, u_1} s).2 (Sigma.snd.{0, u_1} t).2 → HEq.{u_1 + 1} s t
@SerrePositivity.InfinityCategories.stableAugJoinEquiv_heq.{u_1} : ∀ {K L : SSet.{u_1}} {r r' : ℕ},
  Eq.{1} r r' →
    ∀ (x : SerrePositivity.InfinityCategories.Join.augObj.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) r)
      (y : SerrePositivity.InfinityCategories.Join.augObj.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) r'),
      HEq.{u_1 + 1} ((SerrePositivity.InfinityCategories.stableAugJoinEquiv.{u_1} K L r) x)
          ((SerrePositivity.InfinityCategories.stableAugJoinEquiv.{u_1} K L r') y) →
        HEq.{u_1 + 1} x y
SerrePositivity.InfinityCategories.stableAugMap_heq.{u_1} : ∀ (K : SSet.{u_1}) {m m' n n' : ℕ},
  Eq.{1} m m' →
    Eq.{1} n n' →
      ∀ (α : OrderHom.{0, 0} (Fin m) (Fin n)) (β : OrderHom.{0, 0} (Fin m') (Fin n')),
        (∀ (i : Fin m) (j : Fin m'), Eq.{1} ↑i ↑j → Eq.{1} ↑(α i) ↑(β j)) →
          ∀ (x : SerrePositivity.InfinityCategories.Join.augObj.{u_1} K n)
            (y : SerrePositivity.InfinityCategories.Join.augObj.{u_1} K n'),
            HEq.{u_1 + 1} x y →
              HEq.{u_1 + 1} (SerrePositivity.InfinityCategories.Join.augMap.{u_1} K α x)
                (SerrePositivity.InfinityCategories.Join.augMap.{u_1} K β y)
SerrePositivity.InfinityCategories.stableAugReassociation_right_decode.{u_1} : ∀ (K L M : SSet.{u_1}) (r : ℕ)
  (s : SerrePositivity.InfinityCategories.StableAugJoin.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) M r),
  let a :=
    ↑(Sigma.fst.{0, u_1}
        ((SerrePositivity.InfinityCategories.stableAugJoinEquiv.{u_1} K L ↑(Sigma.fst.{0, u_1} s))
          (Sigma.snd.{0, u_1} s).1));
  Eq.{u_1 + 1}
    ((SerrePositivity.InfinityCategories.stableAugJoinEquiv.{u_1} L M (HSub.hSub.{0, 0, 0} r a))
      (Sigma.snd.{0, u_1} ((SerrePositivity.InfinityCategories.stableAugReassociationEquiv.{u_1} K L M r) s)).2)
    (Sigma.mk.{0, u_1} ⟨HSub.hSub.{0, 0, 0} (↑(Sigma.fst.{0, u_1} s)) a, ⋯⟩
      (Prod.mk.{u_1, u_1}
        (Sigma.snd.{0, u_1}
            ((SerrePositivity.InfinityCategories.stableAugJoinEquiv.{u_1} K L ↑(Sigma.fst.{0, u_1} s))
              (Sigma.snd.{0, u_1} s).1)).2
        (cast.{u_1 + 1} ⋯ (Sigma.snd.{0, u_1} s).2)))
SerrePositivity.InfinityCategories.stableAugReassociation_naturality.{u_1} : ∀ (K L M : SSet.{u_1}) {m n : ℕ}
  (α : OrderHom.{0, 0} (Fin m) (Fin n))
  (s : SerrePositivity.InfinityCategories.StableAugJoin.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) M n),
  Eq.{u_1 + 1}
    ((SerrePositivity.InfinityCategories.stableAugReassociationEquiv.{u_1} K L M m)
      (SerrePositivity.InfinityCategories.stableAugJoinMap.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) M α
        s))
    (SerrePositivity.InfinityCategories.stableAugJoinMap.{u_1} K (SerrePositivity.InfinityCategories.join.{u_1} L M) α
      ((SerrePositivity.InfinityCategories.stableAugReassociationEquiv.{u_1} K L M n) s))
SerrePositivity.InfinityCategories.stableAugJoinAssociatorEquiv_naturality.{u_1} : ∀ (K L M : SSet.{u_1}) {m n : ℕ}
  (α : OrderHom.{0, 0} (Fin m) (Fin n))
  (s :
    SerrePositivity.InfinityCategories.Join.augObj.{u_1}
      (SerrePositivity.InfinityCategories.join.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) M) n),
  Eq.{u_1 + 1}
    ((SerrePositivity.InfinityCategories.stableAugJoinAssociatorEquiv.{u_1} K L M m)
      (SerrePositivity.InfinityCategories.Join.augMap.{u_1}
        (SerrePositivity.InfinityCategories.join.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) M) α s))
    (SerrePositivity.InfinityCategories.Join.augMap.{u_1}
      (SerrePositivity.InfinityCategories.join.{u_1} K (SerrePositivity.InfinityCategories.join.{u_1} L M)) α
      ((SerrePositivity.InfinityCategories.stableAugJoinAssociatorEquiv.{u_1} K L M n) s))
SerrePositivity.InfinityCategories.stableJoinAssociatorHom.{u_1} : (K L M : SSet.{u_1}) →
  Quiver.Hom.{u_1, u_1 + 1}
    (SerrePositivity.InfinityCategories.join.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) M)
    (SerrePositivity.InfinityCategories.join.{u_1} K (SerrePositivity.InfinityCategories.join.{u_1} L M))
SerrePositivity.InfinityCategories.stableJoinAssociatorHom_isIso.{u_1} : ∀ (K L M : SSet.{u_1}),
  CategoryTheory.IsIso.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.stableJoinAssociatorHom.{u_1} K L M)
SerrePositivity.InfinityCategories.stableJoinAssociator.{u_1} : (K L M : SSet.{u_1}) →
  CategoryTheory.Iso.{u_1, u_1 + 1}
    (SerrePositivity.InfinityCategories.join.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) M)
    (SerrePositivity.InfinityCategories.join.{u_1} K (SerrePositivity.InfinityCategories.join.{u_1} L M))
@SerrePositivity.InfinityCategories.stableAugJoinHom.{u_1} : {K K' L L' : SSet.{u_1}} →
  Quiver.Hom.{u_1, u_1 + 1} K K' →
    Quiver.Hom.{u_1, u_1 + 1} L L' →
      (r : ℕ) →
        SerrePositivity.InfinityCategories.StableAugJoin.{u_1} K L r →
          SerrePositivity.InfinityCategories.StableAugJoin.{u_1} K' L' r
@SerrePositivity.InfinityCategories.stableAugJoinEquiv_hom.{u_1} : ∀ {K K' L L' : SSet.{u_1}}
  (f : Quiver.Hom.{u_1, u_1 + 1} K K') (g : Quiver.Hom.{u_1, u_1 + 1} L L') (r : ℕ)
  (s : SerrePositivity.InfinityCategories.Join.augObj.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) r),
  Eq.{u_1 + 1}
    ((SerrePositivity.InfinityCategories.stableAugJoinEquiv.{u_1} K' L' r)
      (SerrePositivity.InfinityCategories.Join.augHom.{u_1} (SerrePositivity.InfinityCategories.joinMap.{u_1} f g) r s))
    (SerrePositivity.InfinityCategories.stableAugJoinHom.{u_1} f g r
      ((SerrePositivity.InfinityCategories.stableAugJoinEquiv.{u_1} K L r) s))
@SerrePositivity.InfinityCategories.stableAugHom_heq.{u_1} : ∀ {K L : SSet.{u_1}} (f : Quiver.Hom.{u_1, u_1 + 1} K L)
  {r r' : ℕ},
  Eq.{1} r r' →
    ∀ (x : SerrePositivity.InfinityCategories.Join.augObj.{u_1} K r)
      (y : SerrePositivity.InfinityCategories.Join.augObj.{u_1} K r'),
      HEq.{u_1 + 1} x y →
        HEq.{u_1 + 1} (SerrePositivity.InfinityCategories.Join.augHom.{u_1} f r x)
          (SerrePositivity.InfinityCategories.Join.augHom.{u_1} f r' y)
@SerrePositivity.InfinityCategories.stableAugReassociation_hom.{u_1} : ∀ {K K' L L' M M' : SSet.{u_1}}
  (f : Quiver.Hom.{u_1, u_1 + 1} K K') (g : Quiver.Hom.{u_1, u_1 + 1} L L') (h : Quiver.Hom.{u_1, u_1 + 1} M M') (r : ℕ)
  (s : SerrePositivity.InfinityCategories.StableAugJoin.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) M r),
  Eq.{u_1 + 1}
    ((SerrePositivity.InfinityCategories.stableAugReassociationEquiv.{u_1} K' L' M' r)
      (SerrePositivity.InfinityCategories.stableAugJoinHom.{u_1} (SerrePositivity.InfinityCategories.joinMap.{u_1} f g)
        h r s))
    (SerrePositivity.InfinityCategories.stableAugJoinHom.{u_1} f (SerrePositivity.InfinityCategories.joinMap.{u_1} g h)
      r ((SerrePositivity.InfinityCategories.stableAugReassociationEquiv.{u_1} K L M r) s))
@SerrePositivity.InfinityCategories.stableAugJoinAssociatorEquiv_hom.{u_1} : ∀ {K K' L L' M M' : SSet.{u_1}}
  (f : Quiver.Hom.{u_1, u_1 + 1} K K') (g : Quiver.Hom.{u_1, u_1 + 1} L L') (h : Quiver.Hom.{u_1, u_1 + 1} M M') (r : ℕ)
  (s :
    SerrePositivity.InfinityCategories.Join.augObj.{u_1}
      (SerrePositivity.InfinityCategories.join.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) M) r),
  Eq.{u_1 + 1}
    ((SerrePositivity.InfinityCategories.stableAugJoinAssociatorEquiv.{u_1} K' L' M' r)
      (SerrePositivity.InfinityCategories.Join.augHom.{u_1}
        (SerrePositivity.InfinityCategories.joinMap.{u_1} (SerrePositivity.InfinityCategories.joinMap.{u_1} f g) h) r
        s))
    (SerrePositivity.InfinityCategories.Join.augHom.{u_1}
      (SerrePositivity.InfinityCategories.joinMap.{u_1} f (SerrePositivity.InfinityCategories.joinMap.{u_1} g h)) r
      ((SerrePositivity.InfinityCategories.stableAugJoinAssociatorEquiv.{u_1} K L M r) s))
@SerrePositivity.InfinityCategories.stableJoinAssociator_naturality.{u_1} : ∀ {K K' L L' M M' : SSet.{u_1}}
  (f : Quiver.Hom.{u_1, u_1 + 1} K K') (g : Quiver.Hom.{u_1, u_1 + 1} L L') (h : Quiver.Hom.{u_1, u_1 + 1} M M'),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.joinMap.{u_1} (SerrePositivity.InfinityCategories.joinMap.{u_1} f g) h)
      (CategoryTheory.Iso.hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.stableJoinAssociator.{u_1} K' L' M')))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.Iso.hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.stableJoinAssociator.{u_1} K L M))
      (SerrePositivity.InfinityCategories.joinMap.{u_1} f (SerrePositivity.InfinityCategories.joinMap.{u_1} g h)))
SerrePositivity.InfinityCategories.stableAugJoinInl.{u_1} : (K L : SSet.{u_1}) →
  (r : ℕ) →
    SerrePositivity.InfinityCategories.Join.augObj.{u_1} K r →
      SerrePositivity.InfinityCategories.StableAugJoin.{u_1} K L r
SerrePositivity.InfinityCategories.stableAugJoinInr.{u_1} : (K L : SSet.{u_1}) →
  (r : ℕ) →
    SerrePositivity.InfinityCategories.Join.augObj.{u_1} L r →
      SerrePositivity.InfinityCategories.StableAugJoin.{u_1} K L r
SerrePositivity.InfinityCategories.stableAugJoinEquiv_inl.{u_1} : ∀ (K L : SSet.{u_1}) (r : ℕ)
  (x : SerrePositivity.InfinityCategories.Join.augObj.{u_1} K r),
  Eq.{u_1 + 1}
    ((SerrePositivity.InfinityCategories.stableAugJoinEquiv.{u_1} K L r)
      (SerrePositivity.InfinityCategories.Join.augHom.{u_1} (SerrePositivity.InfinityCategories.joinInl.{u_1} K L) r x))
    (SerrePositivity.InfinityCategories.stableAugJoinInl.{u_1} K L r x)
SerrePositivity.InfinityCategories.stableAugJoinEquiv_inr.{u_1} : ∀ (K L : SSet.{u_1}) (r : ℕ)
  (x : SerrePositivity.InfinityCategories.Join.augObj.{u_1} L r),
  Eq.{u_1 + 1}
    ((SerrePositivity.InfinityCategories.stableAugJoinEquiv.{u_1} K L r)
      (SerrePositivity.InfinityCategories.Join.augHom.{u_1} (SerrePositivity.InfinityCategories.joinInr.{u_1} K L) r x))
    (SerrePositivity.InfinityCategories.stableAugJoinInr.{u_1} K L r x)
SerrePositivity.InfinityCategories.stableAugReassociation_inl.{u_1} : ∀ (K L M : SSet.{u_1}) (r : ℕ)
  (s : SerrePositivity.InfinityCategories.Join.augObj.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) r),
  Eq.{u_1 + 1}
    ((SerrePositivity.InfinityCategories.stableAugReassociationEquiv.{u_1} K L M r)
      (SerrePositivity.InfinityCategories.stableAugJoinInl.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) M r
        s))
    (SerrePositivity.InfinityCategories.stableAugJoinHom.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K)
      (SerrePositivity.InfinityCategories.joinInl.{u_1} L M) r
      ((SerrePositivity.InfinityCategories.stableAugJoinEquiv.{u_1} K L r) s))
SerrePositivity.InfinityCategories.stableJoinAssociator_inl.{u_1} : ∀ (K L M : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.joinInl.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) M)
      (CategoryTheory.Iso.hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.stableJoinAssociator.{u_1} K L M)))
    (SerrePositivity.InfinityCategories.joinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K)
      (SerrePositivity.InfinityCategories.joinInl.{u_1} L M))
SerrePositivity.InfinityCategories.stableJoinAssociator_inr.{u_1} : ∀ (K L M : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.joinInr.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) M)
      (CategoryTheory.Iso.hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.stableJoinAssociator.{u_1} K L M)))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.joinInr.{u_1} L M)
      (SerrePositivity.InfinityCategories.joinInr.{u_1} K (SerrePositivity.InfinityCategories.join.{u_1} L M)))
```


## S4：二重 coslice の同型と余極限余錐の coslice 制限

対象 `ColimitCosliceRestriction` と集約 `Stable` のビルドは成功（2027 jobs）。
全宣言監査は 83 モジュール・906 宣言で標準三公理のみ。
join の中間因子の包含との可換性、任意パラメーターの二重 coslice の Hom の同値、
その自然性と実際の単体集合の同型を構成した。余錐全体から基底への coslice 制限は
uncurry により基底包含による制限と厳密に一致し、頂点射影とも可換。
余極限性とこの制限の trivial Kan fibration 性の同値は、値域の quasicategory 性を仮定しない。
次の義務は図式の pushout に沿う制限の充填と、左四角形・四頂点図式から五頂点図式への適用。
従って貼り合わせ本体、三角構造・S5〜S7 は未完了。

```lean
SerrePositivity.InfinityCategories.stableAugEmpty_heq.{u_1} : ∀ (K : SSet.{u_1}) {r : ℕ},
  Eq.{1} r 0 →
    ∀ (x : SerrePositivity.InfinityCategories.Join.augObj.{u_1} K r),
      HEq.{u_1 + 1} x
        (have this := PUnit.unit.{u_1 + 1};
        this)
SerrePositivity.InfinityCategories.stableAugReassociation_middle.{u_1} : ∀ (K L M : SSet.{u_1}) (r : ℕ)
  (s : SerrePositivity.InfinityCategories.StableAugJoin.{u_1} K M r),
  Eq.{u_1 + 1}
    ((SerrePositivity.InfinityCategories.stableAugReassociationEquiv.{u_1} K L M r)
      (SerrePositivity.InfinityCategories.stableAugJoinHom.{u_1} (SerrePositivity.InfinityCategories.joinInl.{u_1} K L)
        (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} M) r s))
    (SerrePositivity.InfinityCategories.stableAugJoinHom.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K)
      (SerrePositivity.InfinityCategories.joinInr.{u_1} L M) r s)
SerrePositivity.InfinityCategories.stableJoinAssociator_middle.{u_1} : ∀ (K L M : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.joinMap.{u_1} (SerrePositivity.InfinityCategories.joinInl.{u_1} K L)
        (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} M))
      (CategoryTheory.Iso.hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.stableJoinAssociator.{u_1} K L M)))
    (SerrePositivity.InfinityCategories.joinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K)
      (SerrePositivity.InfinityCategories.joinInr.{u_1} L M))
SerrePositivity.InfinityCategories.stableJoinAssociator_middle_inv.{u_1} : ∀ (K L M : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.joinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K)
        (SerrePositivity.InfinityCategories.joinInr.{u_1} L M))
      (CategoryTheory.Iso.inv.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.stableJoinAssociator.{u_1} K L M)))
    (SerrePositivity.InfinityCategories.joinMap.{u_1} (SerrePositivity.InfinityCategories.joinInl.{u_1} K L)
      (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} M))
SerrePositivity.InfinityCategories.stableJoinAssociator_inl_inv.{u_1} : ∀ (K L M : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.joinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K)
        (SerrePositivity.InfinityCategories.joinInl.{u_1} L M))
      (CategoryTheory.Iso.inv.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.stableJoinAssociator.{u_1} K L M)))
    (SerrePositivity.InfinityCategories.joinInl.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) M)
SerrePositivity.InfinityCategories.stableJoinAssociator_leftLeft_inv.{u_1} : ∀ (K L M : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.joinInl.{u_1} K (SerrePositivity.InfinityCategories.join.{u_1} L M))
      (CategoryTheory.Iso.inv.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.stableJoinAssociator.{u_1} K L M)))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.joinInl.{u_1} K L)
      (SerrePositivity.InfinityCategories.joinInl.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L) M))
@SerrePositivity.InfinityCategories.stableJoinAssociator_inv_naturality.{u_1} : ∀ {K K' L L' M M' : SSet.{u_1}}
  (f : Quiver.Hom.{u_1, u_1 + 1} K K') (g : Quiver.Hom.{u_1, u_1 + 1} L L') (h : Quiver.Hom.{u_1, u_1 + 1} M M'),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.joinMap.{u_1} f (SerrePositivity.InfinityCategories.joinMap.{u_1} g h))
      (CategoryTheory.Iso.inv.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.stableJoinAssociator.{u_1} K' L' M')))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.Iso.inv.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.stableJoinAssociator.{u_1} K L M))
      (SerrePositivity.InfinityCategories.joinMap.{u_1} (SerrePositivity.InfinityCategories.joinMap.{u_1} f g) h))
@SerrePositivity.InfinityCategories.nestedCosliceDiagramCurry.{u_1} : {K X : SSet.{u_1}} →
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} →
    (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p) →
      (A : SSet.{u_1}) →
        (Subtype.{u_1 + 1} fun F =>
            Eq.{u_1 + 1}
              (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
                (SerrePositivity.InfinityCategories.joinInl.{u_1}
                  (SerrePositivity.InfinityCategories.join.{u_1} K
                    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
                  A)
                F)
              ↑c) →
          Subtype.{u_1 + 1} fun G =>
            Eq.{u_1 + 1}
              (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
                (SerrePositivity.InfinityCategories.joinInl.{u_1}
                  (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }) A)
                G)
              ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1}) c)
@SerrePositivity.InfinityCategories.nestedCosliceDiagramUncurry.{u_1} : {K X : SSet.{u_1}} →
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} →
    (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p) →
      (A : SSet.{u_1}) →
        (Subtype.{u_1 + 1} fun G =>
            Eq.{u_1 + 1}
              (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
                (SerrePositivity.InfinityCategories.joinInl.{u_1}
                  (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }) A)
                G)
              ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1}) c)) →
          Subtype.{u_1 + 1} fun F =>
            Eq.{u_1 + 1}
              (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
                (SerrePositivity.InfinityCategories.joinInl.{u_1}
                  (SerrePositivity.InfinityCategories.join.{u_1} K
                    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
                  A)
                F)
              ↑c
@SerrePositivity.InfinityCategories.nestedCosliceDiagramEquiv.{u_1} : {K X : SSet.{u_1}} →
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} →
    (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p) →
      (A : SSet.{u_1}) →
        Equiv.{u_1 + 1, u_1 + 1}
          (Subtype.{u_1 + 1} fun F =>
            Eq.{u_1 + 1}
              (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
                (SerrePositivity.InfinityCategories.joinInl.{u_1}
                  (SerrePositivity.InfinityCategories.join.{u_1} K
                    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
                  A)
                F)
              ↑c)
          (Subtype.{u_1 + 1} fun G =>
            Eq.{u_1 + 1}
              (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
                (SerrePositivity.InfinityCategories.joinInl.{u_1}
                  (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }) A)
                G)
              ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1}) c))
@SerrePositivity.InfinityCategories.nestedCosliceHomEquiv.{u_1} : {K X : SSet.{u_1}} →
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} →
    (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p) →
      (A : SSet.{u_1}) →
        Equiv.{u_1 + 1, u_1 + 1} (Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.sliceUnder.{u_1} ↑c))
          (Quiver.Hom.{u_1, u_1 + 1} A
            (SerrePositivity.InfinityCategories.sliceUnder.{u_1}
              ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1})
                (have this := c;
                this))))
@SerrePositivity.InfinityCategories.nestedCosliceHomEquiv_doubleUncurry.{u_1} : ∀ {K X A : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p)
  (f : Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.sliceUnder.{u_1} ↑c)),
  Eq.{u_1 + 1}
    (SerrePositivity.InfinityCategories.sliceUnderUncurry.{u_1}
      (SerrePositivity.InfinityCategories.sliceUnderUncurry.{u_1}
        ((SerrePositivity.InfinityCategories.nestedCosliceHomEquiv.{u_1} c A) f)))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.Iso.inv.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.stableJoinAssociator.{u_1} K
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }) A))
      (SerrePositivity.InfinityCategories.sliceUnderUncurry.{u_1} f))
@SerrePositivity.InfinityCategories.nestedCosliceHomEquiv_naturality.{u_1} : ∀ {K X A B : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p)
  (f : Quiver.Hom.{u_1, u_1 + 1} A B)
  (g : Quiver.Hom.{u_1, u_1 + 1} B (SerrePositivity.InfinityCategories.sliceUnder.{u_1} ↑c)),
  Eq.{u_1 + 1}
    ((SerrePositivity.InfinityCategories.nestedCosliceHomEquiv.{u_1} c A)
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} f g))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} f
      ((SerrePositivity.InfinityCategories.nestedCosliceHomEquiv.{u_1} c B) g))
@SerrePositivity.InfinityCategories.nestedCosliceIso.{u_1} : {K X : SSet.{u_1}} →
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} →
    (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p) →
      CategoryTheory.Iso.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.sliceUnder.{u_1} ↑c)
        (SerrePositivity.InfinityCategories.sliceUnder.{u_1}
          ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1})
            (have this := c;
            this)))
@SerrePositivity.InfinityCategories.colimitCosliceRestriction.{u_1} : {K X : SSet.{u_1}} →
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} →
    (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p) →
      Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.sliceUnder.{u_1} ↑c)
        (SerrePositivity.InfinityCategories.sliceUnder.{u_1} p)
@SerrePositivity.InfinityCategories.colimitCosliceRestriction_trivialKanFibration.{u_1} : ∀ {K X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p),
  SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c →
    SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1}
      (SerrePositivity.InfinityCategories.colimitCosliceRestriction.{u_1} c)
@SerrePositivity.InfinityCategories.colimitCosliceRestriction_uncurry.{u_1} : ∀ {K X A : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p)
  (f : Quiver.Hom.{u_1, u_1 + 1} A (SerrePositivity.InfinityCategories.sliceUnder.{u_1} ↑c)),
  Eq.{u_1 + 1}
    (SerrePositivity.InfinityCategories.sliceUnderUncurry.{u_1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} f
        (SerrePositivity.InfinityCategories.colimitCosliceRestriction.{u_1} c)))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.joinMap.{u_1}
        (SerrePositivity.InfinityCategories.joinInl.{u_1} K
          (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
        (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} A))
      (SerrePositivity.InfinityCategories.sliceUnderUncurry.{u_1} f))
@SerrePositivity.InfinityCategories.colimitCosliceRestriction_projection.{u_1} : ∀ {K X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.colimitCosliceRestriction.{u_1} c)
      (SerrePositivity.InfinityCategories.sliceUnderProjection.{u_1} p))
    (SerrePositivity.InfinityCategories.sliceUnderProjection.{u_1} ↑c)
@SerrePositivity.InfinityCategories.isColimitCone_iff_colimitCosliceRestriction.{u_1} : ∀ {K X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p),
  SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c ↔
    SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1}
      (SerrePositivity.InfinityCategories.colimitCosliceRestriction.{u_1} c)
```
