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
