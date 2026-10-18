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
