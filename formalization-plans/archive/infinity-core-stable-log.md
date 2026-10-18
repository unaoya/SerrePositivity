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


## S4：余極限余錐の pushout による付加と押し出し四角形の貼り合わせ

対象 `Pasting` と集約 `Stable` のビルドは成功（2034 jobs）。
全宣言監査は 90 モジュール・976 宣言で標準三公理のみ。
余極限余錐を図式の任意の pushout に沿って付加した場合、残りの図式への
coslice 制限が任意の部分複体包含を持ち上げることを直接証明した。
形状の射の単射性・値域の quasicategory 性は不要。余極限性の保存と反映の段階で
値域の quasicategory 性を仮定する。
左四角形・共通 span・四頂点図式の pushout 分解と標準形の包含の一致を通じ、
五頂点図式から四頂点図式への制限へ適用した。
`isPushoutSquare_pasting_iff` は、任意の quasicategory に値を持つ長方形について
左四角形が押し出しなら右が押し出し iff 外側が押し出しとなる。
押し出しの合成と左・外側から右を判定する系も公開。HTT Lemma 4.4.2.1 の押し出し側は完了。
引き戻しへの双対化、h C の三角構造・S5〜S7 は未完了。

```lean
@SerrePositivity.InfinityCategories.cosliceRestriction_lift_of_colimit_attachment.{u_1} : ∀ {K C D X A : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p),
  SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c →
    ∀ (i : Quiver.Hom.{u_1, u_1 + 1} K C)
      (j :
        Quiver.Hom.{u_1, u_1 + 1}
          (SerrePositivity.InfinityCategories.join.{u_1} K
            (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
          D)
      (k : Quiver.Hom.{u_1, u_1 + 1} C D),
      CategoryTheory.IsPushout.{u_1, u_1 + 1}
          (SerrePositivity.InfinityCategories.joinInl.{u_1} K
            (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
          i j k →
        ∀ (F : Quiver.Hom.{u_1, u_1 + 1} D X),
          Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} j F) ↑c →
            ∀ (A₀ : SSet.Subcomplex.{u_1} A),
              CategoryTheory.HasLiftingProperty.{u_1, u_1 + 1} (SSet.Subcomplex.ι.{u_1} A₀)
                (SerrePositivity.InfinityCategories.sliceUnderRestrict.{u_1} F k)
@SerrePositivity.InfinityCategories.cosliceRestriction_trivialKanFibration_of_colimit_attachment.{u_1} : ∀
  {K C D X : SSet.{u_1}} {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p),
  SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c →
    ∀ (i : Quiver.Hom.{u_1, u_1 + 1} K C)
      (j :
        Quiver.Hom.{u_1, u_1 + 1}
          (SerrePositivity.InfinityCategories.join.{u_1} K
            (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
          D)
      (k : Quiver.Hom.{u_1, u_1 + 1} C D),
      CategoryTheory.IsPushout.{u_1, u_1 + 1}
          (SerrePositivity.InfinityCategories.joinInl.{u_1} K
            (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
          i j k →
        ∀ (F : Quiver.Hom.{u_1, u_1 + 1} D X),
          Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} j F) ↑c →
            SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1}
              (SerrePositivity.InfinityCategories.sliceUnderRestrict.{u_1} F k)
@SerrePositivity.InfinityCategories.isColimitCone_iff_restrict_of_colimit_attachment.{u_1} : ∀ {K C D X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X] {p : Quiver.Hom.{u_1, u_1 + 1} K X}
  (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p),
  SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c →
    ∀ (i : Quiver.Hom.{u_1, u_1 + 1} K C)
      (j :
        Quiver.Hom.{u_1, u_1 + 1}
          (SerrePositivity.InfinityCategories.join.{u_1} K
            (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
          D)
      (k : Quiver.Hom.{u_1, u_1 + 1} C D),
      CategoryTheory.IsPushout.{u_1, u_1 + 1}
          (SerrePositivity.InfinityCategories.joinInl.{u_1} K
            (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
          i j k →
        ∀ {F : Quiver.Hom.{u_1, u_1 + 1} D X},
          Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} j F) ↑c →
            ∀ (d : SerrePositivity.InfinityCategories.JoinCocone.{u_1} F),
              SerrePositivity.InfinityCategories.IsColimitCone.{u_1} d ↔
                SerrePositivity.InfinityCategories.IsColimitCone.{u_1}
                  (SerrePositivity.InfinityCategories.JoinCocone.restrict.{u_1} d k)
SerrePositivity.InfinityCategories.pastingLeftSquare.{u_1} : SSet.Subcomplex.{u_1}
  (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
SerrePositivity.InfinityCategories.pastingLeftSpan.{u_1} : SSet.Subcomplex.{u_1}
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingOuterBase.{u_1})
SerrePositivity.InfinityCategories.pastingLeftSquare_le_corner.{u_1} : LE.le.{u_1}
  SerrePositivity.InfinityCategories.pastingLeftSquare.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1}
SerrePositivity.InfinityCategories.pastingLeftSquare_sup_outerBase.{u_1} : Eq.{u_1 + 1}
  (SerrePositivity.InfinityCategories.pastingLeftSquare.{u_1} ⊔
    SerrePositivity.InfinityCategories.pastingOuterBase.{u_1})
  SerrePositivity.InfinityCategories.pastingCorner.{u_1}
SerrePositivity.InfinityCategories.pastingLeftSpanToSquare.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingLeftSpan.{u_1})
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingLeftSquare.{u_1})
SerrePositivity.InfinityCategories.pastingLeftSpanInfIso.{u_1} : CategoryTheory.Iso.{u_1, u_1 + 1}
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingLeftSpan.{u_1})
  (SSet.Subcomplex.toSSet.{u_1}
    (SerrePositivity.InfinityCategories.pastingLeftSquare.{u_1} ⊓
      SerrePositivity.InfinityCategories.pastingOuterBase.{u_1}))
SerrePositivity.InfinityCategories.pastingLeftSpan_isPushout.{u_1} : CategoryTheory.IsPushout.{u_1, u_1 + 1}
  SerrePositivity.InfinityCategories.pastingLeftSpanToSquare.{u_1}
  (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingLeftSpan.{u_1})
  (SSet.Subcomplex.homOfLE.{u_1} SerrePositivity.InfinityCategories.pastingLeftSquare_le_corner.{u_1})
  SerrePositivity.InfinityCategories.pastingOuterBaseToCorner.{u_1}
SerrePositivity.InfinityCategories.pastingLeftProjectOrderHom : OrderHom.{0, 0} (Fin 3) (Fin 2)
SerrePositivity.InfinityCategories.pastingLeftSquareFromStandard.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingLeftSquare.{u_1})
SerrePositivity.InfinityCategories.pastingLeftSquareToStandard.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingLeftSquare.{u_1})
  (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
SerrePositivity.InfinityCategories.pastingLeftSquareIso.{u_1} : CategoryTheory.Iso.{u_1, u_1 + 1}
  (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingLeftSquare.{u_1})
SerrePositivity.InfinityCategories.pastingLeftSquareIso_hom_ι.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (CategoryTheory.Iso.hom.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.pastingLeftSquareIso.{u_1})
    (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingLeftSquare.{u_1}))
  (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_1 + 1}
    (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} 2)
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
SerrePositivity.InfinityCategories.pastingLeftLowerOrderHom : OrderHom.{0, 0} (Fin 3) (Fin 3)
@SerrePositivity.InfinityCategories.pastingLeftLowerSimplex.{u_1} : {n : Opposite.{1} SimplexCategory} →
  CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 }) n →
    CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 }) n
SerrePositivity.InfinityCategories.pastingLeftRaiseOrderHom : OrderHom.{0, 0} (Fin 3) (Fin 3)
@SerrePositivity.InfinityCategories.pastingLeftRaiseSimplex.{u_1} : {n : Opposite.{1} SimplexCategory} →
  CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 }) n →
    CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 }) n
SerrePositivity.InfinityCategories.pastingLeftSpanToRight.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingLeftSpan.{u_1})
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1})
SerrePositivity.InfinityCategories.pastingRightSpanToLeft.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1})
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingLeftSpan.{u_1})
SerrePositivity.InfinityCategories.pastingLeftSpanRightIso.{u_1} : CategoryTheory.Iso.{u_1, u_1 + 1}
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingLeftSpan.{u_1})
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingRightSpan.{u_1})
SerrePositivity.InfinityCategories.pastingLeftSpanIso.{u_1} : CategoryTheory.Iso.{u_1, u_1 + 1}
  (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 0))
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingLeftSpan.{u_1})
SerrePositivity.InfinityCategories.pastingLeftSpanIso_hom_ι.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (CategoryTheory.Iso.hom.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.pastingLeftSpanIso.{u_1})
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingLeftSpan.{u_1})
      (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingOuterBase.{u_1})))
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.spanSquareBoundary.{u_1}
    (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_1 + 1}
      (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} 2)
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })))
SerrePositivity.InfinityCategories.pastingLeftSpanIso_toSquare.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (CategoryTheory.Iso.hom.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.pastingLeftSpanIso.{u_1})
    SerrePositivity.InfinityCategories.pastingLeftSpanToSquare.{u_1})
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.spanSquareBoundary.{u_1}
    (CategoryTheory.Iso.hom.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.pastingLeftSquareIso.{u_1}))
SerrePositivity.InfinityCategories.pastingLeftAttachmentCone.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (SerrePositivity.InfinityCategories.join.{u_1} (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 0))
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
  (SSet.Subcomplex.toSSet.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1})
SerrePositivity.InfinityCategories.pastingLeftAttachment_isPushout.{u_1} : CategoryTheory.IsPushout.{u_1, u_1 + 1}
  (SerrePositivity.InfinityCategories.joinInl.{u_1} (SSet.Subcomplex.toSSet.{u_1} (SSet.horn.{u_1} 2 0))
    (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }))
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (CategoryTheory.Iso.hom.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.pastingLeftSpanIso.{u_1})
    (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingLeftSpan.{u_1}))
  SerrePositivity.InfinityCategories.pastingLeftAttachmentCone.{u_1}
  SerrePositivity.InfinityCategories.pastingOuterBaseToCorner.{u_1}
SerrePositivity.InfinityCategories.pastingLeftAttachmentCone_ι.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.pastingLeftAttachmentCone.{u_1}
    (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1}))
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (CategoryTheory.Iso.hom.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.spanCoconeSquareIso.{u_1})
    (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_1 + 1}
      (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} 2)
      (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })))
@SerrePositivity.InfinityCategories.pastingCornerRestrict_outerBase_trivialKanFibration.{u_1} : ∀ {X : SSet.{u_1}}
  (F :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X),
  SerrePositivity.InfinityCategories.IsPushoutSquare.{u_1}
      (SerrePositivity.InfinityCategories.pastingSquare.{u_1} F 2) →
    SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1}
      (SerrePositivity.InfinityCategories.sliceUnderRestrict.{u_1}
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
          (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.pastingCorner.{u_1}) F)
        SerrePositivity.InfinityCategories.pastingOuterBaseToCorner.{u_1})
@SerrePositivity.InfinityCategories.pastingCocone_isColimitCone_iff_outerCocone.{u_1} : ∀ {X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X]
  (F :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X),
  SerrePositivity.InfinityCategories.IsPushoutSquare.{u_1}
      (SerrePositivity.InfinityCategories.pastingSquare.{u_1} F 2) →
    (SerrePositivity.InfinityCategories.IsColimitCone.{u_1} (SerrePositivity.InfinityCategories.pastingCocone.{u_1} F) ↔
      SerrePositivity.InfinityCategories.IsColimitCone.{u_1}
        (SerrePositivity.InfinityCategories.pastingOuterCocone.{u_1} F))
@SerrePositivity.InfinityCategories.isPushoutSquare_pasting_iff.{u_1} : ∀ {X : SSet.{u_1}} [SSet.Quasicategory.{u_1} X]
  (F :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X),
  SerrePositivity.InfinityCategories.IsPushoutSquare.{u_1}
      (SerrePositivity.InfinityCategories.pastingSquare.{u_1} F 2) →
    (SerrePositivity.InfinityCategories.IsPushoutSquare.{u_1}
        (SerrePositivity.InfinityCategories.pastingSquare.{u_1} F 0) ↔
      SerrePositivity.InfinityCategories.IsPushoutSquare.{u_1}
        (SerrePositivity.InfinityCategories.pastingSquare.{u_1} F 1))
@SerrePositivity.InfinityCategories.isPushoutSquare_pasting.{u_1} : ∀ {X : SSet.{u_1}} [SSet.Quasicategory.{u_1} X]
  (F :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X),
  SerrePositivity.InfinityCategories.IsPushoutSquare.{u_1}
      (SerrePositivity.InfinityCategories.pastingSquare.{u_1} F 2) →
    SerrePositivity.InfinityCategories.IsPushoutSquare.{u_1}
        (SerrePositivity.InfinityCategories.pastingSquare.{u_1} F 0) →
      SerrePositivity.InfinityCategories.IsPushoutSquare.{u_1}
        (SerrePositivity.InfinityCategories.pastingSquare.{u_1} F 1)
@SerrePositivity.InfinityCategories.isPushoutSquare_pasting_cancel_left.{u_1} : ∀ {X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X]
  (F :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X),
  SerrePositivity.InfinityCategories.IsPushoutSquare.{u_1}
      (SerrePositivity.InfinityCategories.pastingSquare.{u_1} F 2) →
    SerrePositivity.InfinityCategories.IsPushoutSquare.{u_1}
        (SerrePositivity.InfinityCategories.pastingSquare.{u_1} F 1) →
      SerrePositivity.InfinityCategories.IsPushoutSquare.{u_1}
        (SerrePositivity.InfinityCategories.pastingSquare.{u_1} F 0)
```


## S4：join・slice・極限錐の反転

対象 `ConeOpposite` と集約 `Stable` のビルドは成功（2044 jobs）。
全宣言監査は 100 モジュール・1056 宣言で標準三公理のみ。
join の反転同型、空次数を含む自然性、因子の射と左右の包含との両立を構成した。
slice の反転は反転した図式の coslice に単体集合として同型であり、頂点射影とも厳密に可換。
任意の錐 c に反転した余錐 reverseCocone を作り、
IsLimitCone c iff IsColimitCone c.reverseCocone を値域の追加仮定なしに証明した。
反転した余錐の頂点は opObjEquiv による元の頂点の反転に一致する。
標準四角形の span／cospan の反転の照合と、長方形の面の反転への接続は未完了。
従って引き戻しの貼り合わせ、三角構造・S5〜S7 は未完了。

```lean
@SerrePositivity.InfinityCategories.stableReverseOrderHom : {m n : ℕ} →
  OrderHom.{0, 0} (Fin m) (Fin n) → OrderHom.{0, 0} (Fin m) (Fin n)
SerrePositivity.InfinityCategories.stableAugOpEquiv.{u_1} : (K : SSet.{u_1}) →
  (r : ℕ) →
    Equiv.{u_1 + 1, u_1 + 1} (SerrePositivity.InfinityCategories.Join.augObj.{u_1} (SSet.op.{u_1} K) r)
      (SerrePositivity.InfinityCategories.Join.augObj.{u_1} K r)
SerrePositivity.InfinityCategories.stableAugOpEquiv_naturality.{u_1} : ∀ (K : SSet.{u_1}) {m n : ℕ}
  (α : OrderHom.{0, 0} (Fin m) (Fin n)) (x : SerrePositivity.InfinityCategories.Join.augObj.{u_1} (SSet.op.{u_1} K) n),
  Eq.{u_1 + 1}
    ((SerrePositivity.InfinityCategories.stableAugOpEquiv.{u_1} K m)
      (SerrePositivity.InfinityCategories.Join.augMap.{u_1} (SSet.op.{u_1} K) α x))
    (SerrePositivity.InfinityCategories.Join.augMap.{u_1} K (SerrePositivity.InfinityCategories.stableReverseOrderHom α)
      ((SerrePositivity.InfinityCategories.stableAugOpEquiv.{u_1} K n) x))
@SerrePositivity.InfinityCategories.stablePullCut_reverse : ∀ {m n : ℕ} (α : OrderHom.{0, 0} (Fin m) (Fin n)) (a : ℕ),
  LE.le.{0} a n →
    Eq.{1}
      (SerrePositivity.InfinityCategories.Join.pullCut (SerrePositivity.InfinityCategories.stableReverseOrderHom α) a)
      (HSub.hSub.{0, 0, 0} m (SerrePositivity.InfinityCategories.Join.pullCut α (HSub.hSub.{0, 0, 0} n a)))
SerrePositivity.InfinityCategories.stableComplementCutEquiv : (r : ℕ) →
  Equiv.{1, 1} (Fin (HAdd.hAdd.{0, 0, 0} r 1)) (Fin (HAdd.hAdd.{0, 0, 0} r 1))
SerrePositivity.InfinityCategories.stableAugJoinReverseFiberEquiv.{u_1} : (K L : SSet.{u_1}) →
  (r : ℕ) →
    (a : Fin (HAdd.hAdd.{0, 0, 0} r 1)) →
      Equiv.{u_1 + 1, u_1 + 1}
        (Prod.{u_1, u_1} (SerrePositivity.InfinityCategories.Join.augObj.{u_1} K ↑a)
          (SerrePositivity.InfinityCategories.Join.augObj.{u_1} L (HSub.hSub.{0, 0, 0} r ↑a)))
        (Prod.{u_1, u_1}
          (SerrePositivity.InfinityCategories.Join.augObj.{u_1} (SSet.op.{u_1} L)
            ↑((SerrePositivity.InfinityCategories.stableComplementCutEquiv r) a))
          (SerrePositivity.InfinityCategories.Join.augObj.{u_1} (SSet.op.{u_1} K)
            (HSub.hSub.{0, 0, 0} r ↑((SerrePositivity.InfinityCategories.stableComplementCutEquiv r) a))))
SerrePositivity.InfinityCategories.stableAugJoinReversePairEquiv.{u_1} : (K L : SSet.{u_1}) →
  (r : ℕ) →
    Equiv.{u_1 + 1, u_1 + 1} (SerrePositivity.InfinityCategories.StableAugJoin.{u_1} K L r)
      (SerrePositivity.InfinityCategories.StableAugJoin.{u_1} (SSet.op.{u_1} L) (SSet.op.{u_1} K) r)
SerrePositivity.InfinityCategories.stableAugJoinReversePair_cut.{u_1} : ∀ (K L : SSet.{u_1}) (r : ℕ)
  (s : SerrePositivity.InfinityCategories.StableAugJoin.{u_1} K L r),
  Eq.{1} (↑(Sigma.fst.{0, u_1} ((SerrePositivity.InfinityCategories.stableAugJoinReversePairEquiv.{u_1} K L r) s)))
    (HSub.hSub.{0, 0, 0} r ↑(Sigma.fst.{0, u_1} s))
SerrePositivity.InfinityCategories.stableAugJoinReversePair_left.{u_1} : ∀ (K L : SSet.{u_1}) (r : ℕ)
  (s : SerrePositivity.InfinityCategories.StableAugJoin.{u_1} K L r),
  Eq.{u_1 + 1}
    ((SerrePositivity.InfinityCategories.stableAugOpEquiv.{u_1} L (HSub.hSub.{0, 0, 0} r ↑(Sigma.fst.{0, u_1} s)))
      (Sigma.snd.{0, u_1} ((SerrePositivity.InfinityCategories.stableAugJoinReversePairEquiv.{u_1} K L r) s)).1)
    (Sigma.snd.{0, u_1} s).2
SerrePositivity.InfinityCategories.stableAugJoinReversePair_right.{u_1} : ∀ (K L : SSet.{u_1}) (r : ℕ)
  (s : SerrePositivity.InfinityCategories.StableAugJoin.{u_1} K L r),
  Eq.{u_1 + 1}
    ((SerrePositivity.InfinityCategories.stableAugOpEquiv.{u_1} K
        (HSub.hSub.{0, 0, 0} r (HSub.hSub.{0, 0, 0} r ↑(Sigma.fst.{0, u_1} s))))
      (Sigma.snd.{0, u_1} ((SerrePositivity.InfinityCategories.stableAugJoinReversePairEquiv.{u_1} K L r) s)).2)
    (cast.{u_1 + 1} ⋯ (Sigma.snd.{0, u_1} s).1)
SerrePositivity.InfinityCategories.stableAugJoinReverseEquiv.{u_1} : (K L : SSet.{u_1}) →
  (r : ℕ) →
    Equiv.{u_1 + 1, u_1 + 1}
      (SerrePositivity.InfinityCategories.Join.augObj.{u_1}
        (SSet.op.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L)) r)
      (SerrePositivity.InfinityCategories.Join.augObj.{u_1}
        (SerrePositivity.InfinityCategories.join.{u_1} (SSet.op.{u_1} L) (SSet.op.{u_1} K)) r)
@SerrePositivity.InfinityCategories.stableReverseRightMap_val : ∀ {m n : ℕ} (α : OrderHom.{0, 0} (Fin m) (Fin n))
  (a : ℕ),
  LE.le.{0} a n →
    ∀
      (i :
        Fin
          (HSub.hSub.{0, 0, 0} m
            (SerrePositivity.InfinityCategories.Join.pullCut
              (SerrePositivity.InfinityCategories.stableReverseOrderHom α) a)))
      (j : Fin (SerrePositivity.InfinityCategories.Join.pullCut α (HSub.hSub.{0, 0, 0} n a))),
      Eq.{1} ↑i ↑j →
        Eq.{1}
          ↑((SerrePositivity.InfinityCategories.Join.rightMap
                (SerrePositivity.InfinityCategories.stableReverseOrderHom α) a)
              i)
          ↑((SerrePositivity.InfinityCategories.stableReverseOrderHom
                (SerrePositivity.InfinityCategories.Join.leftMap α (HSub.hSub.{0, 0, 0} n a)))
              j)
@SerrePositivity.InfinityCategories.stableReverseLeftMap_val : ∀ {m n : ℕ} (α : OrderHom.{0, 0} (Fin m) (Fin n))
  (a : ℕ),
  LE.le.{0} a n →
    ∀
      (i :
        Fin
          (SerrePositivity.InfinityCategories.Join.pullCut (SerrePositivity.InfinityCategories.stableReverseOrderHom α)
            a))
      (j : Fin (HSub.hSub.{0, 0, 0} m (SerrePositivity.InfinityCategories.Join.pullCut α (HSub.hSub.{0, 0, 0} n a)))),
      Eq.{1} ↑i ↑j →
        Eq.{1}
          ↑((SerrePositivity.InfinityCategories.Join.leftMap
                (SerrePositivity.InfinityCategories.stableReverseOrderHom α) a)
              i)
          ↑((SerrePositivity.InfinityCategories.stableReverseOrderHom
                (SerrePositivity.InfinityCategories.Join.rightMap α (HSub.hSub.{0, 0, 0} n a)))
              j)
SerrePositivity.InfinityCategories.stableAugOpEquiv_heq.{u_1} : ∀ (K : SSet.{u_1}) {r r' : ℕ},
  Eq.{1} r r' →
    ∀ (x : SerrePositivity.InfinityCategories.Join.augObj.{u_1} (SSet.op.{u_1} K) r)
      (y : SerrePositivity.InfinityCategories.Join.augObj.{u_1} (SSet.op.{u_1} K) r'),
      HEq.{u_1 + 1} ((SerrePositivity.InfinityCategories.stableAugOpEquiv.{u_1} K r) x)
          ((SerrePositivity.InfinityCategories.stableAugOpEquiv.{u_1} K r') y) →
        HEq.{u_1 + 1} x y
SerrePositivity.InfinityCategories.stableAugJoinReversePair_naturality.{u_1} : ∀ (K L : SSet.{u_1}) {m n : ℕ}
  (α : OrderHom.{0, 0} (Fin m) (Fin n)) (s : SerrePositivity.InfinityCategories.StableAugJoin.{u_1} K L n),
  Eq.{u_1 + 1}
    ((SerrePositivity.InfinityCategories.stableAugJoinReversePairEquiv.{u_1} K L m)
      (SerrePositivity.InfinityCategories.stableAugJoinMap.{u_1} K L
        (SerrePositivity.InfinityCategories.stableReverseOrderHom α) s))
    (SerrePositivity.InfinityCategories.stableAugJoinMap.{u_1} (SSet.op.{u_1} L) (SSet.op.{u_1} K) α
      ((SerrePositivity.InfinityCategories.stableAugJoinReversePairEquiv.{u_1} K L n) s))
SerrePositivity.InfinityCategories.stableAugJoinReverseEquiv_naturality.{u_1} : ∀ (K L : SSet.{u_1}) {m n : ℕ}
  (α : OrderHom.{0, 0} (Fin m) (Fin n))
  (s :
    SerrePositivity.InfinityCategories.Join.augObj.{u_1}
      (SSet.op.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L)) n),
  Eq.{u_1 + 1}
    ((SerrePositivity.InfinityCategories.stableAugJoinReverseEquiv.{u_1} K L m)
      (SerrePositivity.InfinityCategories.Join.augMap.{u_1}
        (SSet.op.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L)) α s))
    (SerrePositivity.InfinityCategories.Join.augMap.{u_1}
      (SerrePositivity.InfinityCategories.join.{u_1} (SSet.op.{u_1} L) (SSet.op.{u_1} K)) α
      ((SerrePositivity.InfinityCategories.stableAugJoinReverseEquiv.{u_1} K L n) s))
SerrePositivity.InfinityCategories.stableJoinReverseHom.{u_1} : (K L : SSet.{u_1}) →
  Quiver.Hom.{u_1, u_1 + 1} (SSet.op.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L))
    (SerrePositivity.InfinityCategories.join.{u_1} (SSet.op.{u_1} L) (SSet.op.{u_1} K))
SerrePositivity.InfinityCategories.stableJoinReverseHom_isIso.{u_1} : ∀ (K L : SSet.{u_1}),
  CategoryTheory.IsIso.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.stableJoinReverseHom.{u_1} K L)
SerrePositivity.InfinityCategories.stableJoinReverseIso.{u_1} : (K L : SSet.{u_1}) →
  CategoryTheory.Iso.{u_1, u_1 + 1} (SSet.op.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L))
    (SerrePositivity.InfinityCategories.join.{u_1} (SSet.op.{u_1} L) (SSet.op.{u_1} K))
@SerrePositivity.InfinityCategories.stableAugOpEquiv_hom.{u_1} : ∀ {K L : SSet.{u_1}}
  (f : Quiver.Hom.{u_1, u_1 + 1} K L) (r : ℕ)
  (x : SerrePositivity.InfinityCategories.Join.augObj.{u_1} (SSet.op.{u_1} K) r),
  Eq.{u_1 + 1}
    ((SerrePositivity.InfinityCategories.stableAugOpEquiv.{u_1} L r)
      (SerrePositivity.InfinityCategories.Join.augHom.{u_1}
        (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} f) r x))
    (SerrePositivity.InfinityCategories.Join.augHom.{u_1} f r
      ((SerrePositivity.InfinityCategories.stableAugOpEquiv.{u_1} K r) x))
@SerrePositivity.InfinityCategories.stableAugJoinReversePair_hom.{u_1} : ∀ {K K' L L' : SSet.{u_1}}
  (f : Quiver.Hom.{u_1, u_1 + 1} K K') (g : Quiver.Hom.{u_1, u_1 + 1} L L') (r : ℕ)
  (s : SerrePositivity.InfinityCategories.StableAugJoin.{u_1} K L r),
  Eq.{u_1 + 1}
    ((SerrePositivity.InfinityCategories.stableAugJoinReversePairEquiv.{u_1} K' L' r)
      (SerrePositivity.InfinityCategories.stableAugJoinHom.{u_1} f g r s))
    (SerrePositivity.InfinityCategories.stableAugJoinHom.{u_1}
      (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} g)
      (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} f) r
      ((SerrePositivity.InfinityCategories.stableAugJoinReversePairEquiv.{u_1} K L r) s))
@SerrePositivity.InfinityCategories.stableAugJoinReverseEquiv_hom.{u_1} : ∀ {K K' L L' : SSet.{u_1}}
  (f : Quiver.Hom.{u_1, u_1 + 1} K K') (g : Quiver.Hom.{u_1, u_1 + 1} L L') (r : ℕ)
  (s :
    SerrePositivity.InfinityCategories.Join.augObj.{u_1}
      (SSet.op.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} K L)) r),
  Eq.{u_1 + 1}
    ((SerrePositivity.InfinityCategories.stableAugJoinReverseEquiv.{u_1} K' L' r)
      (SerrePositivity.InfinityCategories.Join.augHom.{u_1}
        (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1}
          (SerrePositivity.InfinityCategories.joinMap.{u_1} f g))
        r s))
    (SerrePositivity.InfinityCategories.Join.augHom.{u_1}
      (SerrePositivity.InfinityCategories.joinMap.{u_1}
        (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} g)
        (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} f))
      r ((SerrePositivity.InfinityCategories.stableAugJoinReverseEquiv.{u_1} K L r) s))
@SerrePositivity.InfinityCategories.stableJoinReverse_naturality.{u_1} : ∀ {K K' L L' : SSet.{u_1}}
  (f : Quiver.Hom.{u_1, u_1 + 1} K K') (g : Quiver.Hom.{u_1, u_1 + 1} L L'),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1}
        (SerrePositivity.InfinityCategories.joinMap.{u_1} f g))
      (CategoryTheory.Iso.hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.stableJoinReverseIso.{u_1} K' L')))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.Iso.hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.stableJoinReverseIso.{u_1} K L))
      (SerrePositivity.InfinityCategories.joinMap.{u_1}
        (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} g)
        (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} f)))
SerrePositivity.InfinityCategories.stableJoinReverse_inl.{u_1} : ∀ (K L : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1}
        (SerrePositivity.InfinityCategories.joinInl.{u_1} K L))
      (CategoryTheory.Iso.hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.stableJoinReverseIso.{u_1} K L)))
    (SerrePositivity.InfinityCategories.joinInr.{u_1} (SSet.op.{u_1} L) (SSet.op.{u_1} K))
SerrePositivity.InfinityCategories.stableJoinReverse_inr.{u_1} : ∀ (K L : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1}
        (SerrePositivity.InfinityCategories.joinInr.{u_1} K L))
      (CategoryTheory.Iso.hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.stableJoinReverseIso.{u_1} K L)))
    (SerrePositivity.InfinityCategories.joinInl.{u_1} (SSet.op.{u_1} L) (SSet.op.{u_1} K))
SerrePositivity.InfinityCategories.stableJoinReverse_inr_inv.{u_1} : ∀ (K L : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.joinInr.{u_1} (SSet.op.{u_1} L) (SSet.op.{u_1} K))
      (CategoryTheory.Iso.inv.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.stableJoinReverseIso.{u_1} K L)))
    (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1}
      (SerrePositivity.InfinityCategories.joinInl.{u_1} K L))
SerrePositivity.InfinityCategories.stableJoinReverse_inl_inv.{u_1} : ∀ (K L : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.joinInl.{u_1} (SSet.op.{u_1} L) (SSet.op.{u_1} K))
      (CategoryTheory.Iso.inv.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.stableJoinReverseIso.{u_1} K L)))
    (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1}
      (SerrePositivity.InfinityCategories.joinInr.{u_1} K L))
SerrePositivity.InfinityCategories.coneDiagramReverseHomEquiv.{u_1} : (A K X : SSet.{u_1}) →
  Equiv.{u_1 + 1, u_1 + 1} (Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.join.{u_1} A K) X)
    (Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.join.{u_1} (SSet.op.{u_1} K) (SSet.op.{u_1} A))
      (SSet.op.{u_1} X))
SerrePositivity.InfinityCategories.coneDiagramReverseHomEquiv_apply.{u_1} : ∀ (A K X : SSet.{u_1})
  (F : Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.join.{u_1} A K) X),
  Eq.{u_1 + 1} ((SerrePositivity.InfinityCategories.coneDiagramReverseHomEquiv.{u_1} A K X) F)
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.Iso.inv.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.stableJoinReverseIso.{u_1} A K))
      (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} F))
@SerrePositivity.InfinityCategories.coneDiagramReverse_fixed_iff.{u_1} : ∀ {A K X : SSet.{u_1}}
  (p : Quiver.Hom.{u_1, u_1 + 1} K X)
  (F : Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.join.{u_1} A K) X),
  Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.joinInr.{u_1} A K) F) p ↔
    Eq.{u_1 + 1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (SerrePositivity.InfinityCategories.joinInl.{u_1} (SSet.op.{u_1} K) (SSet.op.{u_1} A))
        ((SerrePositivity.InfinityCategories.coneDiagramReverseHomEquiv.{u_1} A K X) F))
      (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} p)
@SerrePositivity.InfinityCategories.coneDiagramReverseEquiv.{u_1} : {K X : SSet.{u_1}} →
  (p : Quiver.Hom.{u_1, u_1 + 1} K X) →
    (A : SSet.{u_1}) →
      Equiv.{u_1 + 1, u_1 + 1}
        (Subtype.{u_1 + 1} fun F =>
          Eq.{u_1 + 1}
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.joinInr.{u_1} A K) F)
            p)
        (Subtype.{u_1 + 1} fun G =>
          Eq.{u_1 + 1}
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
              (SerrePositivity.InfinityCategories.joinInl.{u_1} (SSet.op.{u_1} K) (SSet.op.{u_1} A)) G)
            (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} p))
@SerrePositivity.InfinityCategories.stableJoinReverse_inv_naturality.{u_1} : ∀ {K K' L L' : SSet.{u_1}}
  (f : Quiver.Hom.{u_1, u_1 + 1} K K') (g : Quiver.Hom.{u_1, u_1 + 1} L L'),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.joinMap.{u_1}
        (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} g)
        (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} f))
      (CategoryTheory.Iso.inv.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.stableJoinReverseIso.{u_1} K' L')))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.Iso.inv.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.stableJoinReverseIso.{u_1} K L))
      (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1}
        (SerrePositivity.InfinityCategories.joinMap.{u_1} f g)))
@SerrePositivity.InfinityCategories.coneDiagramReverseEquiv_naturality.{u_1} : ∀ {A B K X : SSet.{u_1}}
  (p : Quiver.Hom.{u_1, u_1 + 1} K X) (f : Quiver.Hom.{u_1, u_1 + 1} A B)
  (F :
    Subtype.{u_1 + 1} fun F =>
      Eq.{u_1 + 1}
        (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.joinInr.{u_1} B K) F) p),
  Eq.{u_1 + 1}
    (↑((SerrePositivity.InfinityCategories.coneDiagramReverseEquiv.{u_1} p A)
        (Subtype.mk.{u_1 + 1}
          (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
            (SerrePositivity.InfinityCategories.joinMap.{u_1} f (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} K)) ↑F)
          ⋯)))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.joinMap.{u_1}
        (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} (SSet.op.{u_1} K))
        (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} f))
      ↑((SerrePositivity.InfinityCategories.coneDiagramReverseEquiv.{u_1} p B) F))
@SerrePositivity.InfinityCategories.stableStdSimplex_opIso_inv_naturality.{u_1} : ∀ {a b : SimplexCategory}
  (α : Quiver.Hom.{0, 0} a b),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.Iso.inv.{u_1, u_1 + 1} (SSet.stdSimplex.opIso.{u_1} a))
      (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1}
        (CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1}
          (CategoryTheory.Functor.map.{0, 0, 0, 0} SimplexCategory.rev α))))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.Functor.map.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} α)
      (CategoryTheory.Iso.inv.{u_1, u_1 + 1} (SSet.stdSimplex.opIso.{u_1} b)))
@SerrePositivity.InfinityCategories.cosliceDiagramReparamEquiv.{u_1} : {K X A B : SSet.{u_1}} →
  (p : Quiver.Hom.{u_1, u_1 + 1} K X) →
    CategoryTheory.Iso.{u_1, u_1 + 1} A B →
      Equiv.{u_1 + 1, u_1 + 1}
        (Subtype.{u_1 + 1} fun F =>
          Eq.{u_1 + 1}
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.joinInl.{u_1} K A) F)
            p)
        (Subtype.{u_1 + 1} fun G =>
          Eq.{u_1 + 1}
            (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.joinInl.{u_1} K B) G)
            p)
@SerrePositivity.InfinityCategories.sliceOverOpObjEquiv.{u_1} : {K X : SSet.{u_1}} →
  (p : Quiver.Hom.{u_1, u_1 + 1} K X) →
    (n : SimplexCategory) →
      Equiv.{u_1 + 1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
          (SSet.op.{u_1} (SerrePositivity.InfinityCategories.sliceOver.{u_1} p)) (Opposite.op.{1} n))
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
          (SerrePositivity.InfinityCategories.sliceUnder.{u_1}
            (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} p))
          (Opposite.op.{1} n))
@SerrePositivity.InfinityCategories.sliceOverOpObjEquiv_val.{u_1} : ∀ {K X : SSet.{u_1}}
  (p : Quiver.Hom.{u_1, u_1 + 1} K X) (n : SimplexCategory)
  (s :
    CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1}
      (SSet.op.{u_1} (SerrePositivity.InfinityCategories.sliceOver.{u_1} p)) (Opposite.op.{1} n)),
  Eq.{u_1 + 1} (↑((SerrePositivity.InfinityCategories.sliceOverOpObjEquiv.{u_1} p n) s))
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.joinMap.{u_1}
        (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} (SSet.op.{u_1} K))
        (CategoryTheory.Iso.inv.{u_1, u_1 + 1} (SSet.stdSimplex.opIso.{u_1} n)))
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (CategoryTheory.Iso.inv.{u_1, u_1 + 1}
          (SerrePositivity.InfinityCategories.stableJoinReverseIso.{u_1}
            (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} n) K))
        (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} ↑(SSet.opObjEquiv.{u_1} s))))
@SerrePositivity.InfinityCategories.sliceOverOpMap.{u_1} : {K X : SSet.{u_1}} →
  (p : Quiver.Hom.{u_1, u_1 + 1} K X) →
    Quiver.Hom.{u_1, u_1 + 1} (SSet.op.{u_1} (SerrePositivity.InfinityCategories.sliceOver.{u_1} p))
      (SerrePositivity.InfinityCategories.sliceUnder.{u_1}
        (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} p))
@SerrePositivity.InfinityCategories.sliceOverOpMap_isIso.{u_1} : ∀ {K X : SSet.{u_1}}
  (p : Quiver.Hom.{u_1, u_1 + 1} K X),
  CategoryTheory.IsIso.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.sliceOverOpMap.{u_1} p)
@SerrePositivity.InfinityCategories.sliceOverOpIso.{u_1} : {K X : SSet.{u_1}} →
  (p : Quiver.Hom.{u_1, u_1 + 1} K X) →
    CategoryTheory.Iso.{u_1, u_1 + 1} (SSet.op.{u_1} (SerrePositivity.InfinityCategories.sliceOver.{u_1} p))
      (SerrePositivity.InfinityCategories.sliceUnder.{u_1}
        (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} p))
@SerrePositivity.InfinityCategories.stableReverseSimplex_yoneda.{u_1} : ∀ {X : SSet.{u_1}} (n : SimplexCategory)
  (F : Quiver.Hom.{u_1, u_1 + 1} (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} n) X),
  Eq.{u_1 + 1}
    (SSet.yonedaEquiv.{u_1}
      (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
        (CategoryTheory.Iso.inv.{u_1, u_1 + 1} (SSet.stdSimplex.opIso.{u_1} n))
        (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} F)))
    ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.opObjEquiv.{u_1}) (SSet.yonedaEquiv.{u_1} F))
@SerrePositivity.InfinityCategories.sliceOverOpIso_projection.{u_1} : ∀ {K X : SSet.{u_1}}
  (p : Quiver.Hom.{u_1, u_1 + 1} K X),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (CategoryTheory.Iso.hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.sliceOverOpIso.{u_1} p))
      (SerrePositivity.InfinityCategories.sliceUnderProjection.{u_1}
        (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} p)))
    (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1}
      (SerrePositivity.InfinityCategories.sliceOverProjection.{u_1} p))
@SerrePositivity.InfinityCategories.IsInitialVertex.map_of_isIso.{u_1} : ∀ {X Y : SSet.{u_1}}
  (q : Quiver.Hom.{u_1, u_1 + 1} X Y) [CategoryTheory.IsIso.{u_1, u_1 + 1} q]
  {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })},
  SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} x →
    SerrePositivity.InfinityCategories.IsInitialVertex.{u_1}
      ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
          (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1} q (Opposite.op.{1} { len := 0 })))
        x)
@SerrePositivity.InfinityCategories.isInitialVertex_iff_of_isIso.{u_1} : ∀ {X Y : SSet.{u_1}}
  (q : Quiver.Hom.{u_1, u_1 + 1} X Y) [CategoryTheory.IsIso.{u_1, u_1 + 1} q]
  (x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })),
  SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} x ↔
    SerrePositivity.InfinityCategories.IsInitialVertex.{u_1}
      ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
          (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1} q (Opposite.op.{1} { len := 0 })))
        x)
@SerrePositivity.InfinityCategories.isTerminalVertex_iff_isInitialVertex_op.{u_1} : ∀ {X : SSet.{u_1}}
  (x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })),
  SerrePositivity.InfinityCategories.IsTerminalVertex.{u_1} x ↔
    SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.opObjEquiv.{u_1}) x)
@SerrePositivity.InfinityCategories.JoinCone.reverseCocone.{u_1} : {K X : SSet.{u_1}} →
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} →
    SerrePositivity.InfinityCategories.JoinCone.{u_1} p →
      SerrePositivity.InfinityCategories.JoinCocone.{u_1}
        (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.opFunctor.{u_1} p)
@SerrePositivity.InfinityCategories.isLimitCone_iff_reverseCocone.{u_1} : ∀ {K X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} (c : SerrePositivity.InfinityCategories.JoinCone.{u_1} p),
  SerrePositivity.InfinityCategories.IsLimitCone.{u_1} c ↔
    SerrePositivity.InfinityCategories.IsColimitCone.{u_1}
      (SerrePositivity.InfinityCategories.JoinCone.reverseCocone.{u_1} c)
@SerrePositivity.InfinityCategories.JoinCone.reverseCocone_vertex.{u_1} : ∀ {K X : SSet.{u_1}}
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} (c : SerrePositivity.InfinityCategories.JoinCone.{u_1} p),
  Eq.{u_1 + 1}
    (SerrePositivity.InfinityCategories.JoinCocone.vertex.{u_1}
      (SerrePositivity.InfinityCategories.JoinCone.reverseCocone.{u_1} c))
    ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.opObjEquiv.{u_1}) (SerrePositivity.InfinityCategories.JoinCone.vertex.{u_1} c))
```

## S4：標準格子と長方形の面の反転

任意の値域 X と自然数 m,n。追加の quasicategory 仮定なし。
正確な公開型（Lean の出力）：

```lean
SerrePositivity.InfinityCategories.reverseGrid.{u} {X : SSet.{u}} {m n : ℕ}
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[m] Δ[n]) X) :
  Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[m] Δ[n]) (SSet.op.{u} X)
SerrePositivity.InfinityCategories.reverseGrid_postcomp.{u} {X Y : SSet.{u}} {m n : ℕ}
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[m] Δ[n]) X) (p : Quiver.Hom.{u, u + 1} X Y) :
  Eq.{u + 1} (SerrePositivity.InfinityCategories.reverseGrid.{u} (CategoryStruct.comp.{u, u + 1} F p))
    (CategoryStruct.comp.{u, u + 1} (SerrePositivity.InfinityCategories.reverseGrid.{u} F)
      (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} opFunctor.{u} p))
SerrePositivity.InfinityCategories.reverseGrid_double.{u} {X : SSet.{u}} {m n : ℕ}
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[m] Δ[n]) X) :
  Eq.{u + 1}
    (CategoryStruct.comp.{u, u + 1}
      (SerrePositivity.InfinityCategories.reverseGrid.{u} (SerrePositivity.InfinityCategories.reverseGrid.{u} F))
      (Iso.hom.{u, u + 1} (Iso.app.{u, u, u + 1, u + 1} opFunctorCompOpFunctorIso.{u} X)))
    F
SerrePositivity.InfinityCategories.reverseGrid_pastingSquare.{u} {X : SSet.{u}}
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[2] Δ[1]) X) (i : Fin 3) :
  Eq.{u + 1}
    (SerrePositivity.InfinityCategories.pastingSquare.{u} (SerrePositivity.InfinityCategories.reverseGrid.{u} F) i)
    (SerrePositivity.InfinityCategories.reverseGrid.{u} (SerrePositivity.InfinityCategories.pastingSquare.{u} F i.rev))
```

対象ビルド 1614 jobs、Stable 集約ビルド 2045 jobs とも終了コード 0。
公理監査は 101 モジュール・1060 宣言について標準三公理のみ、終了コード 0。
`git diff --check` 成功。普遍四角形の反転との照合、引き戻しの貼り合わせ、
三角構造および S5〜S7 は未完了。

## S4：標準四角形の双対性と引き戻しの貼り合わせ

標準四角形の反転と余極限の同型による再添字付けには値域の追加仮定なし。
貼り合わせの三定理には値域の Quasicategory と右四角形の引き戻し性を仮定する。
正確な公開型（Lean の出力）：

```lean
SerrePositivity.InfinityCategories.isColimitCone_iff_restrict_of_isIso.{u} {K₀ K X : SSet.{u}}
  {p : Quiver.Hom.{u, u + 1} K X} (c : SerrePositivity.InfinityCategories.JoinCocone.{u} p)
  (f : Quiver.Hom.{u, u + 1} K₀ K) [IsIso.{u, u + 1} f] :
  SerrePositivity.InfinityCategories.IsColimitCone.{u} c ↔
    SerrePositivity.InfinityCategories.IsColimitCone.{u}
      (SerrePositivity.InfinityCategories.JoinCocone.restrict.{u} c f)
SerrePositivity.InfinityCategories.isLimitCone_iff_reverseCocone_restrict.{u} {K L X : SSet.{u}}
  {p : Quiver.Hom.{u, u + 1} K X} (c : SerrePositivity.InfinityCategories.JoinCone.{u} p)
  (f : Quiver.Hom.{u, u + 1} L (SSet.op.{u} K)) [IsIso.{u, u + 1} f] :
  SerrePositivity.InfinityCategories.IsLimitCone.{u} c ↔
    SerrePositivity.InfinityCategories.IsColimitCone.{u}
      (SerrePositivity.InfinityCategories.JoinCocone.restrict.{u}
        (SerrePositivity.InfinityCategories.JoinCone.reverseCocone.{u} c) f)
SerrePositivity.InfinityCategories.stableJoinReverse_stdSimplex_zero_one.{u} :
  Eq.{u + 1}
    (CategoryStruct.comp.{u, u + 1}
      (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} opFunctor.{u}
        (Iso.inv.{u, u + 1} (SerrePositivity.InfinityCategories.joinStdSimplexIso.{u} 0 1)))
      (CategoryStruct.comp.{u, u + 1}
        (Iso.hom.{u, u + 1} (SerrePositivity.InfinityCategories.stableJoinReverseIso.{u} Δ[0] Δ[1]))
        (CategoryStruct.comp.{u, u + 1}
          (SerrePositivity.InfinityCategories.joinMap.{u} (Iso.hom.{u, u + 1} (stdSimplex.opIso.{u} ⦋1⦌))
            (Iso.hom.{u, u + 1} (stdSimplex.opIso.{u} ⦋0⦌)))
          (Iso.hom.{u, u + 1} (SerrePositivity.InfinityCategories.joinStdSimplexIso.{u} 1 0)))))
    (Iso.hom.{u, u + 1} (stdSimplex.opIso.{u} ⦋2⦌))
SerrePositivity.InfinityCategories.stableJoinReverse_stdSimplex_zero_one_inv.{u} :
  Eq.{u + 1}
    (CategoryStruct.comp.{u, u + 1}
      (SerrePositivity.InfinityCategories.joinMap.{u} (Iso.inv.{u, u + 1} (stdSimplex.opIso.{u} ⦋1⦌))
        (Iso.inv.{u, u + 1} (stdSimplex.opIso.{u} ⦋0⦌)))
      (CategoryStruct.comp.{u, u + 1}
        (Iso.inv.{u, u + 1} (SerrePositivity.InfinityCategories.stableJoinReverseIso.{u} Δ[0] Δ[1]))
        (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} opFunctor.{u}
          (Iso.hom.{u, u + 1} (SerrePositivity.InfinityCategories.joinStdSimplexIso.{u} 0 1)))))
    (CategoryStruct.comp.{u, u + 1} (Iso.hom.{u, u + 1} (SerrePositivity.InfinityCategories.joinStdSimplexIso.{u} 1 0))
      (Iso.inv.{u, u + 1} (stdSimplex.opIso.{u} ⦋2⦌)))
SerrePositivity.InfinityCategories.stableJoinReverse_stdSimplex_zero_one_inv_triangle.{u} :
  Eq.{u + 1}
    (CategoryStruct.comp.{u, u + 1} (Iso.inv.{u, u + 1} (SerrePositivity.InfinityCategories.joinStdSimplexIso.{u} 1 0))
      (CategoryStruct.comp.{u, u + 1}
        (SerrePositivity.InfinityCategories.joinMap.{u} (Iso.inv.{u, u + 1} (stdSimplex.opIso.{u} ⦋1⦌))
          (Iso.inv.{u, u + 1} (stdSimplex.opIso.{u} ⦋0⦌)))
        (Iso.inv.{u, u + 1} (SerrePositivity.InfinityCategories.stableJoinReverseIso.{u} Δ[0] Δ[1]))))
    (CategoryStruct.comp.{u, u + 1} (Iso.inv.{u, u + 1} (stdSimplex.opIso.{u} ⦋2⦌))
      (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} opFunctor.{u}
        (Iso.inv.{u, u + 1} (SerrePositivity.InfinityCategories.joinStdSimplexIso.{u} 0 1))))
SerrePositivity.InfinityCategories.stableHornReverse_two_left.{u} :
  Eq.{u + 1}
    (CategoryStruct.comp.{u, u + 1} horn₂₀.ι₀₁.{u}
      (Iso.hom.{u, u + 1} (SerrePositivity.InfinityCategories.hornReverseIso.{u} 2 2)))
    (CategoryStruct.comp.{u, u + 1} (Iso.inv.{u, u + 1} (stdSimplex.opIso.{u} ⦋1⦌))
      (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} opFunctor.{u} horn₂₂.ι₁₂.{u}))
SerrePositivity.InfinityCategories.stableHornReverse_two_right.{u} :
  Eq.{u + 1}
    (CategoryStruct.comp.{u, u + 1} horn₂₀.ι₀₂.{u}
      (Iso.hom.{u, u + 1} (SerrePositivity.InfinityCategories.hornReverseIso.{u} 2 2)))
    (CategoryStruct.comp.{u, u + 1} (Iso.inv.{u, u + 1} (stdSimplex.opIso.{u} ⦋1⦌))
      (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} opFunctor.{u} horn₂₂.ι₀₂.{u}))
SerrePositivity.InfinityCategories.squareConeReverseShape.{u} :
  Quiver.Hom.{u, u + 1} (SerrePositivity.InfinityCategories.join.{u} (Subcomplex.toSSet.{u} Λ[2, 0]) Δ[0])
    (SSet.op.{u} (SerrePositivity.InfinityCategories.join.{u} Δ[0] (Subcomplex.toSSet.{u} Λ[2, 2])))
SerrePositivity.InfinityCategories.squareConeReverseShape_left.{u} :
  Eq.{u + 1}
    (CategoryStruct.comp.{u, u + 1} SerrePositivity.InfinityCategories.spanCoconeTriangleLeft.{u}
      SerrePositivity.InfinityCategories.squareConeReverseShape.{u})
    (CategoryStruct.comp.{u, u + 1} (Iso.inv.{u, u + 1} (stdSimplex.opIso.{u} ⦋2⦌))
      (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} opFunctor.{u}
        SerrePositivity.InfinityCategories.cospanConeTriangleRight.{u}))
SerrePositivity.InfinityCategories.squareConeReverseShape_right.{u} :
  Eq.{u + 1}
    (CategoryStruct.comp.{u, u + 1} SerrePositivity.InfinityCategories.spanCoconeTriangleRight.{u}
      SerrePositivity.InfinityCategories.squareConeReverseShape.{u})
    (CategoryStruct.comp.{u, u + 1} (Iso.inv.{u, u + 1} (stdSimplex.opIso.{u} ⦋2⦌))
      (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} opFunctor.{u}
        SerrePositivity.InfinityCategories.cospanConeTriangleLeft.{u}))
SerrePositivity.InfinityCategories.squareTriangle_reverseGrid.{u} (i : Fin 2) :
  Eq.{u + 1}
    (CategoryStruct.comp.{u, u + 1} (SerrePositivity.InfinityCategories.squareTriangle.{u} i)
      (SerrePositivity.InfinityCategories.reverseGrid.{u}
        (CategoryStruct.id.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]))))
    (CategoryStruct.comp.{u, u + 1} (Iso.inv.{u, u + 1} (stdSimplex.opIso.{u} ⦋2⦌))
      (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} opFunctor.{u}
        (SerrePositivity.InfinityCategories.squareTriangle.{u} i.rev)))
SerrePositivity.InfinityCategories.squareConeReverseShape_square.{u} :
  Eq.{u + 1}
    (CategoryStruct.comp.{u, u + 1} SerrePositivity.InfinityCategories.squareConeReverseShape.{u}
      (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} opFunctor.{u}
        (Iso.hom.{u, u + 1} SerrePositivity.InfinityCategories.cospanConeSquareIso.{u})))
    (CategoryStruct.comp.{u, u + 1} (Iso.hom.{u, u + 1} SerrePositivity.InfinityCategories.spanCoconeSquareIso.{u})
      (SerrePositivity.InfinityCategories.reverseGrid.{u}
        (CategoryStruct.id.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]))))
SerrePositivity.InfinityCategories.JoinCone.reverseCocone_val.{u} {K X : SSet.{u}} {p : Quiver.Hom.{u, u + 1} K X}
  (c : SerrePositivity.InfinityCategories.JoinCone.{u} p) :
  Eq.{u + 1} (↑(SerrePositivity.InfinityCategories.JoinCone.reverseCocone.{u} c))
    (CategoryStruct.comp.{u, u + 1}
      (SerrePositivity.InfinityCategories.joinMap.{u} (CategoryStruct.id.{u, u + 1} (SSet.op.{u} K))
        (Iso.inv.{u, u + 1} (stdSimplex.opIso.{u} ⦋0⦌)))
      (CategoryStruct.comp.{u, u + 1}
        (Iso.inv.{u, u + 1} (SerrePositivity.InfinityCategories.stableJoinReverseIso.{u} Δ[0] K))
        (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} opFunctor.{u} ↑c)))
SerrePositivity.InfinityCategories.isPullbackSquare_iff_reverseGrid.{u} {X : SSet.{u}}
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]) X) :
  SerrePositivity.InfinityCategories.IsPullbackSquare.{u} F ↔
    SerrePositivity.InfinityCategories.IsPushoutSquare.{u} (SerrePositivity.InfinityCategories.reverseGrid.{u} F)
SerrePositivity.InfinityCategories.isPullbackSquare_pasting_iff.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[2] Δ[1]) X)
  (hright :
    SerrePositivity.InfinityCategories.IsPullbackSquare.{u}
      (SerrePositivity.InfinityCategories.pastingSquare.{u} F 0)) :
  SerrePositivity.InfinityCategories.IsPullbackSquare.{u} (SerrePositivity.InfinityCategories.pastingSquare.{u} F 2) ↔
    SerrePositivity.InfinityCategories.IsPullbackSquare.{u} (SerrePositivity.InfinityCategories.pastingSquare.{u} F 1)
SerrePositivity.InfinityCategories.isPullbackSquare_pasting.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[2] Δ[1]) X)
  (hleft :
    SerrePositivity.InfinityCategories.IsPullbackSquare.{u} (SerrePositivity.InfinityCategories.pastingSquare.{u} F 2))
  (hright :
    SerrePositivity.InfinityCategories.IsPullbackSquare.{u}
      (SerrePositivity.InfinityCategories.pastingSquare.{u} F 0)) :
  SerrePositivity.InfinityCategories.IsPullbackSquare.{u} (SerrePositivity.InfinityCategories.pastingSquare.{u} F 1)
SerrePositivity.InfinityCategories.isPullbackSquare_pasting_cancel_right.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[2] Δ[1]) X)
  (hright :
    SerrePositivity.InfinityCategories.IsPullbackSquare.{u} (SerrePositivity.InfinityCategories.pastingSquare.{u} F 0))
  (houter :
    SerrePositivity.InfinityCategories.IsPullbackSquare.{u}
      (SerrePositivity.InfinityCategories.pastingSquare.{u} F 1)) :
  SerrePositivity.InfinityCategories.IsPullbackSquare.{u} (SerrePositivity.InfinityCategories.pastingSquare.{u} F 2)
```

対象 PullbackPasting ビルド 1978 jobs、Stable 集約ビルド 2050 jobs、
公開型の抽出、公理監査はすべて終了コード 0。監査は 106 モジュール・1079 宣言
（生成・非公開宣言を含む）、依存公理は propext・Classical.choice・Quot.sound のみ。
HTT Lemma 4.4.2.1 の押し出し・引き戻しの両側は完了。A6 を待つ箇所はない。
S4 の前加法構造・整数シフト・三角構造（TR1〜TR4）、S5〜S7 は未完了。

## S4：零角の列の短複体と任意の射を含む列

四角形の可換性には値域の仮定なし。零角の短複体とその射には
Quasicategory と任意の HasZeroMorphisms を仮定する。HasZeroVertex からの
標準の零射構造も公開した。全ての h C の射を含む cofiber/fiber 短複体の
存在には Quasicategory と IsStable を仮定する。正確な公開型：

```lean
SerrePositivity.InfinityCategories.hasZeroMorphisms_ho.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  [SerrePositivity.InfinityCategories.HasZeroVertex.{u} X] :
  HasZeroMorphisms.{u, u} ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} X)
SerrePositivity.InfinityCategories.squareBottomArrow.{u} {X : SSet.{u}}
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]) X) :
  Truncated.Edge.{u} (SerrePositivity.InfinityCategories.squareVertex.{u} F 0 0)
    (SerrePositivity.InfinityCategories.squareVertex.{u} F 1 0)
SerrePositivity.InfinityCategories.squareRightArrow.{u} {X : SSet.{u}}
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]) X) :
  Truncated.Edge.{u} (SerrePositivity.InfinityCategories.squareVertex.{u} F 1 0)
    (SerrePositivity.InfinityCategories.squareVertex.{u} F 1 1)
SerrePositivity.InfinityCategories.squareLeftArrow.{u} {X : SSet.{u}}
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]) X) :
  Truncated.Edge.{u} (SerrePositivity.InfinityCategories.squareVertex.{u} F 0 0)
    (SerrePositivity.InfinityCategories.squareVertex.{u} F 0 1)
SerrePositivity.InfinityCategories.squareTopArrow.{u} {X : SSet.{u}}
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]) X) :
  Truncated.Edge.{u} (SerrePositivity.InfinityCategories.squareVertex.{u} F 0 1)
    (SerrePositivity.InfinityCategories.squareVertex.{u} F 1 1)
SerrePositivity.InfinityCategories.square_homMk_comm.{u} {X : SSet.{u}}
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]) X) :
  Eq.{u + 1}
    (CategoryStruct.comp.{u, u}
      (Truncated.HomotopyCategory.homMk.{u} (SerrePositivity.InfinityCategories.squareBottomArrow.{u} F))
      (Truncated.HomotopyCategory.homMk.{u} (SerrePositivity.InfinityCategories.squareRightArrow.{u} F)))
    (CategoryStruct.comp.{u, u}
      (Truncated.HomotopyCategory.homMk.{u} (SerrePositivity.InfinityCategories.squareLeftArrow.{u} F))
      (Truncated.HomotopyCategory.homMk.{u} (SerrePositivity.InfinityCategories.squareTopArrow.{u} F)))
SerrePositivity.InfinityCategories.squareHoVertex.{u} {X : SSet.{u}}
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]) X) (i j : Fin 2) :
  ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} X)
SerrePositivity.InfinityCategories.squareHoBottom.{u} {X : SSet.{u}}
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]) X) :
  Quiver.Hom.{u, u} (SerrePositivity.InfinityCategories.squareHoVertex.{u} F 0 0)
    (SerrePositivity.InfinityCategories.squareHoVertex.{u} F 1 0)
SerrePositivity.InfinityCategories.squareHoRight.{u} {X : SSet.{u}}
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]) X) :
  Quiver.Hom.{u, u} (SerrePositivity.InfinityCategories.squareHoVertex.{u} F 1 0)
    (SerrePositivity.InfinityCategories.squareHoVertex.{u} F 1 1)
SerrePositivity.InfinityCategories.squareHoLeft.{u} {X : SSet.{u}}
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]) X) :
  Quiver.Hom.{u, u} (SerrePositivity.InfinityCategories.squareHoVertex.{u} F 0 0)
    (SerrePositivity.InfinityCategories.squareHoVertex.{u} F 0 1)
SerrePositivity.InfinityCategories.squareHoTop.{u} {X : SSet.{u}}
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]) X) :
  Quiver.Hom.{u, u} (SerrePositivity.InfinityCategories.squareHoVertex.{u} F 0 1)
    (SerrePositivity.InfinityCategories.squareHoVertex.{u} F 1 1)
SerrePositivity.InfinityCategories.ZeroTriangle.homMk_comp_eq_zero.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  [HasZeroMorphisms.{u, u} ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} X)]
  (t : SerrePositivity.InfinityCategories.ZeroTriangle.{u} X) :
  Eq.{u + 1}
    (CategoryStruct.comp.{u, u}
      (SerrePositivity.InfinityCategories.squareHoBottom.{u}
        (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} t))
      (SerrePositivity.InfinityCategories.squareHoRight.{u}
        (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} t)))
    0
SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplex.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  [HasZeroMorphisms.{u, u} ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} X)]
  (t : SerrePositivity.InfinityCategories.ZeroTriangle.{u} X) :
  ShortComplex.{u, u} ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} X)
SerrePositivity.InfinityCategories.squareBottomArrow_edge.{u} {X : SSet.{u}}
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]) X) :
  Eq.{u + 1} (Truncated.Edge.edge.{u} (SerrePositivity.InfinityCategories.squareBottomArrow.{u} F))
    (SSet.yonedaEquiv.{u} (CategoryStruct.comp.{u, u + 1} SerrePositivity.InfinityCategories.squareBottomEdge.{u} F))
SerrePositivity.InfinityCategories.squareRightArrow_edge.{u} {X : SSet.{u}}
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]) X) :
  Eq.{u + 1} (Truncated.Edge.edge.{u} (SerrePositivity.InfinityCategories.squareRightArrow.{u} F))
    (SSet.yonedaEquiv.{u} (CategoryStruct.comp.{u, u + 1} SerrePositivity.InfinityCategories.squareRightEdge.{u} F))
SerrePositivity.InfinityCategories.CofiberSquare.hoShortComplex_f_arrow.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  [HasZeroMorphisms.{u, u} ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} X)] {x y : X _⦋0⦌}
  {f : Truncated.Edge.{u} x y} (s : SerrePositivity.InfinityCategories.CofiberSquare.{u} f) :
  Eq.{u + 1}
    (Arrow.mk.{u, u}
      (ShortComplex.f.{u, u}
        (SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplex.{u}
          (SerrePositivity.InfinityCategories.CofiberSquare.toZeroTriangle.{u} s))))
    (Arrow.mk.{u, u} (Truncated.HomotopyCategory.homMk.{u} f))
SerrePositivity.InfinityCategories.FiberSquare.hoShortComplex_g_arrow.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  [HasZeroMorphisms.{u, u} ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} X)] {x y : X _⦋0⦌}
  {f : Truncated.Edge.{u} x y} (s : SerrePositivity.InfinityCategories.FiberSquare.{u} f) :
  Eq.{u + 1}
    (Arrow.mk.{u, u}
      (ShortComplex.g.{u, u}
        (SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplex.{u}
          (SerrePositivity.InfinityCategories.FiberSquare.toZeroTriangle.{u} s))))
    (Arrow.mk.{u, u} (Truncated.HomotopyCategory.homMk.{u} f))
SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplexMap.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  [HasZeroMorphisms.{u, u} ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} X)]
  (t d : SerrePositivity.InfinityCategories.ZeroTriangle.{u} X)
  (α :
    Quiver.Hom.{u, u}
      (Cat.Hom.toFunctor.{u, u}
        (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
          (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} t)))
      (Cat.Hom.toFunctor.{u, u}
        (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
          (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} d)))) :
  Quiver.Hom.{u, u} (SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplex.{u} t)
    (SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplex.{u} d)
SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplexMap_id.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  [HasZeroMorphisms.{u, u} ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} X)]
  (t : SerrePositivity.InfinityCategories.ZeroTriangle.{u} X) :
  Eq.{u + 1}
    (SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplexMap.{u} t t
      (CategoryStruct.id.{u, u}
        (Cat.Hom.toFunctor.{u, u}
          (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
            (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} t)))))
    (CategoryStruct.id.{u, u} (SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplex.{u} t))
SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplexMap_comp.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  [HasZeroMorphisms.{u, u} ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} X)]
  (t d e : SerrePositivity.InfinityCategories.ZeroTriangle.{u} X)
  (α :
    Quiver.Hom.{u, u}
      (Cat.Hom.toFunctor.{u, u}
        (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
          (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} t)))
      (Cat.Hom.toFunctor.{u, u}
        (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
          (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} d))))
  (β :
    Quiver.Hom.{u, u}
      (Cat.Hom.toFunctor.{u, u}
        (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
          (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} d)))
      (Cat.Hom.toFunctor.{u, u}
        (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
          (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} e)))) :
  Eq.{u + 1}
    (SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplexMap.{u} t e (CategoryStruct.comp.{u, u} α β))
    (CategoryStruct.comp.{u, u} (SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplexMap.{u} t d α)
      (SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplexMap.{u} d e β))
SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplexMapOfHomotopy.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  [HasZeroMorphisms.{u, u} ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} X)]
  (t d : SerrePositivity.InfinityCategories.ZeroTriangle.{u} X)
  (H : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]) Δ[1]) X)
  (h₀ :
    Eq.{u + 1} (CategoryStruct.comp.{u, u + 1} ι₀.{u} H) (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} t))
  (h₁ :
    Eq.{u + 1} (CategoryStruct.comp.{u, u + 1} ι₁.{u} H)
      (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} d)) :
  Quiver.Hom.{u, u} (SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplex.{u} t)
    (SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplex.{u} d)
SerrePositivity.InfinityCategories.exists_cofiber_hoShortComplex.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  [SerrePositivity.InfinityCategories.IsStable.{u} X] {a b : ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} X)}
  (f : Quiver.Hom.{u, u} a b) :
  ∃ t,
    SerrePositivity.InfinityCategories.IsCofiberSequence.{u} t ∧
      Eq.{u + 1}
        (Arrow.mk.{u, u} (ShortComplex.f.{u, u} (SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplex.{u} t)))
        (Arrow.mk.{u, u} f)
SerrePositivity.InfinityCategories.exists_fiber_hoShortComplex.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  [SerrePositivity.InfinityCategories.IsStable.{u} X] {a b : ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} X)}
  (f : Quiver.Hom.{u, u} a b) :
  ∃ t,
    SerrePositivity.InfinityCategories.IsFiberSequence.{u} t ∧
      Eq.{u + 1}
        (Arrow.mk.{u, u} (ShortComplex.g.{u, u} (SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplex.{u} t)))
        (Arrow.mk.{u, u} f)
```

対象 CofiberShortComplex ビルド 1608 jobs、Stable 集約ビルド 2054 jobs、
公開型抽出、公理監査はすべて終了コード 0。監査は 109 モジュール・1106 宣言
（生成・非公開宣言を含む）について標準三公理のみ。`git diff --check` 成功。
これらは短複体とその射まで。接続射 Z → ΣX、前加法構造、整数シフト、
TR1〜TR4、Pretriangulated と S5〜S7 は未完了。

## S4：指定した普遍余錐の部分族・両端を保つ持ち上げ

単射な部分族を保つ延長には値域 Quasicategory と全頂点での余極限の存在を仮定する。
図式間の辺・余錐間のホモトピーへの持ち上げには、値域 Quasicategory と両端の
IsColimitCone のみ。一次元境界の辺の持ち上げ自体には quasicategory 仮定なし。
正確な公開型（Lean の出力）：

```lean
SerrePositivity.InfinityCategories.stableBoundaryPair.{u} {X : SSet.{u}} (x y : X _⦋0⦌) :
  Quiver.Hom.{u, u + 1} (Subcomplex.toSSet.{u} ∂Δ[1]) X
SerrePositivity.InfinityCategories.stableBoundaryPair_zero.{u} {X : SSet.{u}} (x y : X _⦋0⦌) :
  Eq.{u + 1}
    (CategoryStruct.comp.{u, u + 1} (SerrePositivity.InfinityCategories.boundaryVertex.{u} 0 0)
      (SerrePositivity.InfinityCategories.stableBoundaryPair.{u} x y))
    ((Equiv.symm.{u + 1, u + 1} SSet.yonedaEquiv.{u}) x)
SerrePositivity.InfinityCategories.stableBoundaryPair_one.{u} {X : SSet.{u}} (x y : X _⦋0⦌) :
  Eq.{u + 1}
    (CategoryStruct.comp.{u, u + 1} (SerrePositivity.InfinityCategories.boundaryVertex.{u} 0 1)
      (SerrePositivity.InfinityCategories.stableBoundaryPair.{u} x y))
    ((Equiv.symm.{u + 1, u + 1} SSet.yonedaEquiv.{u}) y)
SerrePositivity.InfinityCategories.stableBoundaryPair_hom_ext.{u} {X : SSet.{u}}
  {f g : Quiver.Hom.{u, u + 1} (Subcomplex.toSSet.{u} ∂Δ[1]) X}
  (h₀ :
    Eq.{u + 1} (CategoryStruct.comp.{u, u + 1} (SerrePositivity.InfinityCategories.boundaryVertex.{u} 0 0) f)
      (CategoryStruct.comp.{u, u + 1} (SerrePositivity.InfinityCategories.boundaryVertex.{u} 0 0) g))
  (h₁ :
    Eq.{u + 1} (CategoryStruct.comp.{u, u + 1} (SerrePositivity.InfinityCategories.boundaryVertex.{u} 0 1) f)
      (CategoryStruct.comp.{u, u + 1} (SerrePositivity.InfinityCategories.boundaryVertex.{u} 0 1) g)) :
  Eq.{u + 1} f g
SerrePositivity.InfinityCategories.stableBoundaryPair_postcomp.{u} {X Y : SSet.{u}} (x y : X _⦋0⦌)
  (p : Quiver.Hom.{u, u + 1} X Y) :
  Eq.{u + 1} (CategoryStruct.comp.{u, u + 1} (SerrePositivity.InfinityCategories.stableBoundaryPair.{u} x y) p)
    (SerrePositivity.InfinityCategories.stableBoundaryPair.{u}
      ((ConcreteCategory.hom.{u, u, u + 1, u} (NatTrans.app.{0, u, 0, u + 1} p (Opposite.op.{1} ⦋0⦌))) x)
      ((ConcreteCategory.hom.{u, u, u + 1, u} (NatTrans.app.{0, u, 0, u + 1} p (Opposite.op.{1} ⦋0⦌))) y))
SerrePositivity.InfinityCategories.stableBoundaryPair_edge.{u} {X : SSet.{u}} {x y : X _⦋0⦌}
  (e : Truncated.Edge.{u} x y) :
  Eq.{u + 1} (SerrePositivity.InfinityCategories.stableBoundaryPair.{u} x y)
    (CategoryStruct.comp.{u, u + 1} (Subcomplex.ι.{u} ∂Δ[1])
      ((Equiv.symm.{u + 1, u + 1} SSet.yonedaEquiv.{u}) (Truncated.Edge.edge.{u} e)))
SerrePositivity.InfinityCategories.exists_edge_lift_of_boundary_one.{u} {E B : SSet.{u}} (p : Quiver.Hom.{u, u + 1} E B)
  [HasLiftingProperty.{u, u + 1} (Subcomplex.ι.{u} ∂Δ[1]) p] (x y : E _⦋0⦌)
  (e :
    Truncated.Edge.{u}
      ((ConcreteCategory.hom.{u, u, u + 1, u} (NatTrans.app.{0, u, 0, u + 1} p (Opposite.op.{1} ⦋0⦌))) x)
      ((ConcreteCategory.hom.{u, u, u + 1, u} (NatTrans.app.{0, u, 0, u + 1} p (Opposite.op.{1} ⦋0⦌))) y)) :
  ∃ f, Eq.{u + 1} (Truncated.Edge.map.{u} f (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} (truncation.{u} 2) p)) e
SerrePositivity.InfinityCategories.exists_colimitCoconeFamily_extension.{u} {A₀ A K X : SSet.{u}} [Quasicategory.{u} X]
  (i : Quiver.Hom.{u, u + 1} A₀ A) [Mono.{u, u + 1} i] (d : Quiver.Hom.{u, u + 1} A (K ⟹ X))
  (hd :
    ∀ (a : A _⦋0⦌),
      SerrePositivity.InfinityCategories.HasColimit.{u}
        ((Equiv.symm.{u + 1, u + 1} (SerrePositivity.InfinityCategories.functorVertexEquiv.{u} K X))
          ((ConcreteCategory.hom.{u, u, u + 1, u} (NatTrans.app.{0, u, 0, u + 1} d (Opposite.op.{1} ⦋0⦌))) a)))
  (c : Quiver.Hom.{u, u + 1} A₀ (SerrePositivity.InfinityCategories.colimitCocones.{u} K X))
  (hc :
    Eq.{u + 1} (CategoryStruct.comp.{u, u + 1} c (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u} K X))
      (CategoryStruct.comp.{u, u + 1} i d)) :
  ∃ f,
    Eq.{u + 1} (CategoryStruct.comp.{u, u + 1} i f) c ∧
      Eq.{u + 1} (CategoryStruct.comp.{u, u + 1} f (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u} K X))
        d
SerrePositivity.InfinityCategories.colimitCoconeVertex.{u} {K X : SSet.{u}} [Quasicategory.{u} X]
  {p : Quiver.Hom.{u, u + 1} K X} (c : SerrePositivity.InfinityCategories.JoinCocone.{u} p)
  (hc : SerrePositivity.InfinityCategories.IsColimitCone.{u} c) :
  SerrePositivity.InfinityCategories.colimitCocones.{u} K X _⦋0⦌
SerrePositivity.InfinityCategories.colimitCoconeVertex_projection.{u} {K X : SSet.{u}} [Quasicategory.{u} X]
  {p : Quiver.Hom.{u, u + 1} K X} (c : SerrePositivity.InfinityCategories.JoinCocone.{u} p)
  (hc : SerrePositivity.InfinityCategories.IsColimitCone.{u} c) :
  Eq.{u + 1}
    ((ConcreteCategory.hom.{u, u, u + 1, u}
        (NatTrans.app.{0, u, 0, u + 1} (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u} K X)
          (Opposite.op.{1} ⦋0⦌)))
      (SerrePositivity.InfinityCategories.colimitCoconeVertex.{u} c hc))
    (SerrePositivity.InfinityCategories.functorVertex.{u} p)
SerrePositivity.InfinityCategories.exists_colimitCocone_edge.{u} {K X : SSet.{u}} [Quasicategory.{u} X]
  {p q : Quiver.Hom.{u, u + 1} K X} (c : SerrePositivity.InfinityCategories.JoinCocone.{u} p)
  (d : SerrePositivity.InfinityCategories.JoinCocone.{u} q)
  (hc : SerrePositivity.InfinityCategories.IsColimitCone.{u} c)
  (hd : SerrePositivity.InfinityCategories.IsColimitCone.{u} d)
  (e :
    Truncated.Edge.{u} (SerrePositivity.InfinityCategories.functorVertex.{u} p)
      (SerrePositivity.InfinityCategories.functorVertex.{u} q)) :
  ∃ f,
    Eq.{u + 1}
      (Truncated.Edge.edge.{u}
        (Truncated.Edge.map.{u} f
          (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} (truncation.{u} 2)
            (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u} K X))))
      (Truncated.Edge.edge.{u} e)
SerrePositivity.InfinityCategories.exists_colimitCoconeHomotopy.{u} {K X : SSet.{u}} [Quasicategory.{u} X]
  {p q : Quiver.Hom.{u, u + 1} K X} (c : SerrePositivity.InfinityCategories.JoinCocone.{u} p)
  (d : SerrePositivity.InfinityCategories.JoinCocone.{u} q)
  (hc : SerrePositivity.InfinityCategories.IsColimitCone.{u} c)
  (hd : SerrePositivity.InfinityCategories.IsColimitCone.{u} d)
  (e :
    Truncated.Edge.{u} (SerrePositivity.InfinityCategories.functorVertex.{u} p)
      (SerrePositivity.InfinityCategories.functorVertex.{u} q)) :
  ∃ H,
    Eq.{u + 1}
      (CategoryStruct.comp.{u, u + 1}
        (whiskerRight.{u, u + 1} (SerrePositivity.InfinityCategories.joinInl.{u} K Δ[0]) Δ[1])
        (RelativeMorphism.Homotopy.h.{u} H))
      (uncurry.{u, u + 1} ((Equiv.symm.{u + 1, u + 1} SSet.yonedaEquiv.{u}) (Truncated.Edge.edge.{u} e)))
```

対象 ColimitCoconeEdges ビルド 1974 jobs、Stable 集約ビルド 2058 jobs、
公開型の抽出、公理監査はすべて終了コード 0。監査は 113 モジュール・1120 宣言
（生成・非公開宣言を含む）について標準三公理のみ。`git diff --check` 成功。
cofiber の span から suspension の span への具体的な辺と、持ち上げて得る射の Σ との
比較は未完了。接続射、前加法構造、整数シフト、TR1〜TR4、S5〜S7 は未完了。

## S4：始点固定の suspension 比較と cofiber 列の接続射

終対象への辺の比較と span の比較には Quasicategory と指定終点の終対象性を仮定する。
四角形の比較には元の押し出し四角形と、同じ始点の指定 suspension 四角形を与える。
指定 suspension 頂点への接続射には Quasicategory と任意の HasZeroMorphisms、
実際の Σ への接続射には Quasicategory と IsStable を仮定する。
正確な公開型（Lean の出力）：

```lean
SerrePositivity.InfinityCategories.stableTriangleComparisonShape.{u} :
  Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]) Δ[2]
SerrePositivity.InfinityCategories.stableTriangleComparisonShape_bottom.{u} :
  Eq.{u + 1}
    (CategoryStruct.comp.{u, u + 1} SerrePositivity.InfinityCategories.squareBottomEdge.{u}
      SerrePositivity.InfinityCategories.stableTriangleComparisonShape.{u})
    (CosimplicialObject.δ.{u, u + 1} stdSimplex.{u} 2)
SerrePositivity.InfinityCategories.stableTriangleComparisonShape_top.{u} :
  Eq.{u + 1}
    (CategoryStruct.comp.{u, u + 1} SerrePositivity.InfinityCategories.squareTopEdge.{u}
      SerrePositivity.InfinityCategories.stableTriangleComparisonShape.{u})
    (CosimplicialObject.δ.{u, u + 1} stdSimplex.{u} 1)
SerrePositivity.InfinityCategories.stableTriangleComparisonShape_source.{u} :
  Eq.{u + 1}
    (CategoryStruct.comp.{u, u + 1} (whiskerRight.{u, u + 1} (CosimplicialObject.δ.{u, u + 1} stdSimplex.{u} 1) Δ[1])
      SerrePositivity.InfinityCategories.stableTriangleComparisonShape.{u})
    (CategoryStruct.comp.{u, u + 1} (SemiCartesianMonoidalCategory.snd.{u, u + 1} Δ[0] Δ[1])
      (const.{u} ((Equiv.symm.{u + 1, 1} stdSimplex.obj₀Equiv.{u}) 0)))
SerrePositivity.InfinityCategories.exists_terminalArrowComparison.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  {x y z : X _⦋0⦌} (f : Truncated.Edge.{u} x y) (g : Truncated.Edge.{u} x z)
  (hz : SerrePositivity.InfinityCategories.IsTerminalVertex.{u} z) :
  ∃ H,
    Eq.{u + 1}
      (CategoryStruct.comp.{u, u + 1} (whiskerRight.{u, u + 1} (CosimplicialObject.δ.{u, u + 1} stdSimplex.{u} 1) Δ[1])
        (RelativeMorphism.Homotopy.h.{u} H))
      (CategoryStruct.comp.{u, u + 1} (SemiCartesianMonoidalCategory.snd.{u, u + 1} Δ[0] Δ[1]) (const.{u} x))
SerrePositivity.InfinityCategories.exists_terminalSpanComparison.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  {x y₁ y₂ z₁ z₂ : X _⦋0⦌} (f₁ : Truncated.Edge.{u} x y₁) (f₂ : Truncated.Edge.{u} x y₂) (g₁ : Truncated.Edge.{u} x z₁)
  (g₂ : Truncated.Edge.{u} x z₂) (hz₁ : SerrePositivity.InfinityCategories.IsTerminalVertex.{u} z₁)
  (hz₂ : SerrePositivity.InfinityCategories.IsTerminalVertex.{u} z₂) :
  ∃ H,
    Eq.{u + 1}
      (CategoryStruct.comp.{u, u + 1}
        (whiskerRight.{u, u + 1}
          (CategoryStruct.comp.{u, u + 1} (CosimplicialObject.δ.{u, u + 1} stdSimplex.{u} 1) horn₂₀.ι₀₁.{u}) Δ[1])
        (RelativeMorphism.Homotopy.h.{u} H))
      (CategoryStruct.comp.{u, u + 1} (SemiCartesianMonoidalCategory.snd.{u, u + 1} Δ[0] Δ[1]) (const.{u} x))
SerrePositivity.InfinityCategories.squareLeftArrow_edge.{u} {X : SSet.{u}}
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]) X) :
  Eq.{u + 1} (Truncated.Edge.edge.{u} (SerrePositivity.InfinityCategories.squareLeftArrow.{u} F))
    (SSet.yonedaEquiv.{u} (CategoryStruct.comp.{u, u + 1} SerrePositivity.InfinityCategories.squareLeftEdge.{u} F))
SerrePositivity.InfinityCategories.edgeSpan_squareArrows.{u} {X : SSet.{u}}
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]) X) :
  Eq.{u + 1}
    (SerrePositivity.InfinityCategories.edgeSpan.{u} (SerrePositivity.InfinityCategories.squareBottomArrow.{u} F)
      (SerrePositivity.InfinityCategories.squareLeftArrow.{u} F))
    (SerrePositivity.InfinityCategories.pushoutSpan.{u} F)
SerrePositivity.InfinityCategories.exists_suspensionSpanComparison.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]) X)
  (s :
    SerrePositivity.InfinityCategories.SuspensionSquare.{u}
      (SerrePositivity.InfinityCategories.squareVertex.{u} F 0 0)) :
  ∃ H,
    Eq.{u + 1}
      (CategoryStruct.comp.{u, u + 1}
        (whiskerRight.{u, u + 1}
          (CategoryStruct.comp.{u, u + 1} (CosimplicialObject.δ.{u, u + 1} stdSimplex.{u} 1) horn₂₀.ι₀₁.{u}) Δ[1])
        (RelativeMorphism.Homotopy.h.{u} H))
      (CategoryStruct.comp.{u, u + 1} (SemiCartesianMonoidalCategory.snd.{u, u + 1} Δ[0] Δ[1])
        (const.{u} (SerrePositivity.InfinityCategories.squareVertex.{u} F 0 0)))
SerrePositivity.InfinityCategories.exists_cofiberSuspensionComparison.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]) X)
  (hF : SerrePositivity.InfinityCategories.IsPushoutSquare.{u} F)
  (s :
    SerrePositivity.InfinityCategories.SuspensionSquare.{u}
      (SerrePositivity.InfinityCategories.squareVertex.{u} F 0 0)) :
  ∃ Q,
    Eq.{u + 1}
      (CategoryStruct.comp.{u, u + 1}
        (whiskerRight.{u, u + 1}
          (CategoryStruct.comp.{u, u + 1} (CosimplicialObject.δ.{u, u + 1} stdSimplex.{u} 1)
            SerrePositivity.InfinityCategories.squareBottomEdge.{u})
          Δ[1])
        (RelativeMorphism.Homotopy.h.{u} Q))
      (CategoryStruct.comp.{u, u + 1} (SemiCartesianMonoidalCategory.snd.{u, u + 1} Δ[0] Δ[1])
        (const.{u} (SerrePositivity.InfinityCategories.squareVertex.{u} F 0 0)))
SerrePositivity.InfinityCategories.chosenCofiberSuspensionComparison.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]) X)
  (hF : SerrePositivity.InfinityCategories.IsPushoutSquare.{u} F)
  (s :
    SerrePositivity.InfinityCategories.SuspensionSquare.{u}
      (SerrePositivity.InfinityCategories.squareVertex.{u} F 0 0)) :
  Homotopy.{u} F
    (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u}
      (SerrePositivity.InfinityCategories.SuspensionSquare.toZeroTriangle.{u} s))
SerrePositivity.InfinityCategories.chosenCofiberSuspensionComparison_source.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]) X)
  (hF : SerrePositivity.InfinityCategories.IsPushoutSquare.{u} F)
  (s :
    SerrePositivity.InfinityCategories.SuspensionSquare.{u}
      (SerrePositivity.InfinityCategories.squareVertex.{u} F 0 0)) :
  Eq.{u + 1}
    (CategoryStruct.comp.{u, u + 1}
      (whiskerRight.{u, u + 1}
        (CategoryStruct.comp.{u, u + 1} (CosimplicialObject.δ.{u, u + 1} stdSimplex.{u} 1)
          SerrePositivity.InfinityCategories.squareBottomEdge.{u})
        Δ[1])
      (RelativeMorphism.Homotopy.h.{u}
        (SerrePositivity.InfinityCategories.chosenCofiberSuspensionComparison.{u} F hF s)))
    (CategoryStruct.comp.{u, u + 1} (SemiCartesianMonoidalCategory.snd.{u, u + 1} Δ[0] Δ[1])
      (const.{u} (SerrePositivity.InfinityCategories.squareVertex.{u} F 0 0)))
SerrePositivity.InfinityCategories.cofiberSuspensionShortComplexMap.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  [HasZeroMorphisms.{u, u} ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} X)]
  (t : SerrePositivity.InfinityCategories.ZeroTriangle.{u} X)
  (ht : SerrePositivity.InfinityCategories.IsCofiberSequence.{u} t)
  (s :
    SerrePositivity.InfinityCategories.SuspensionSquare.{u}
      (SerrePositivity.InfinityCategories.squareVertex.{u}
        (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} t) 0 0)) :
  Quiver.Hom.{u, u} (SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplex.{u} t)
    (SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplex.{u}
      (SerrePositivity.InfinityCategories.SuspensionSquare.toZeroTriangle.{u} s))
SerrePositivity.InfinityCategories.cofiberConnectingToSuspension.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  [HasZeroMorphisms.{u, u} ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} X)]
  (t : SerrePositivity.InfinityCategories.ZeroTriangle.{u} X)
  (ht : SerrePositivity.InfinityCategories.IsCofiberSequence.{u} t)
  (s :
    SerrePositivity.InfinityCategories.SuspensionSquare.{u}
      (SerrePositivity.InfinityCategories.squareVertex.{u}
        (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} t) 0 0)) :
  Quiver.Hom.{u, u} (ShortComplex.X₃.{u, u} (SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplex.{u} t))
    (HomotopyCategory.mk.{u} (SerrePositivity.InfinityCategories.SuspensionSquare.vertex.{u} s))
SerrePositivity.InfinityCategories.cofiberConnectingToSuspension_comp_eq_zero.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  [HasZeroMorphisms.{u, u} ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} X)]
  (t : SerrePositivity.InfinityCategories.ZeroTriangle.{u} X)
  (ht : SerrePositivity.InfinityCategories.IsCofiberSequence.{u} t)
  (s :
    SerrePositivity.InfinityCategories.SuspensionSquare.{u}
      (SerrePositivity.InfinityCategories.squareVertex.{u}
        (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} t) 0 0)) :
  Eq.{u + 1}
    (CategoryStruct.comp.{u, u}
      (ShortComplex.g.{u, u} (SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplex.{u} t))
      (SerrePositivity.InfinityCategories.cofiberConnectingToSuspension.{u} t ht s))
    0
SerrePositivity.InfinityCategories.cofiberConnecting.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  [SerrePositivity.InfinityCategories.IsStable.{u} X] (t : SerrePositivity.InfinityCategories.ZeroTriangle.{u} X)
  (ht : SerrePositivity.InfinityCategories.IsCofiberSequence.{u} t) :
  Quiver.Hom.{u, u} (ShortComplex.X₃.{u, u} (SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplex.{u} t))
    (Functor.obj.{u, u, u, u} (SerrePositivity.InfinityCategories.suspensionFunctor.{u} X)
      (ShortComplex.X₁.{u, u} (SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplex.{u} t)))
SerrePositivity.InfinityCategories.cofiberConnecting_comp_eq_zero.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  [SerrePositivity.InfinityCategories.IsStable.{u} X] (t : SerrePositivity.InfinityCategories.ZeroTriangle.{u} X)
  (ht : SerrePositivity.InfinityCategories.IsCofiberSequence.{u} t) :
  Eq.{u + 1}
    (CategoryStruct.comp.{u, u}
      (ShortComplex.g.{u, u} (SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplex.{u} t))
      (SerrePositivity.InfinityCategories.cofiberConnecting.{u} t ht))
    0
```

対象 CofiberConnecting ビルド 1991 jobs、Stable 集約ビルド 2063 jobs、
公開型抽出、公理監査はすべて終了コード 0。監査は 118 モジュール・1143 宣言
（生成・非公開宣言を含む）について標準三公理のみ。`git diff --check` 成功。
接続射の構成と、列の第二射の後に接続射を合成した際の零合成まで完了。
選択独立性、自然性、接続射の後の Σf との零合成、前加法構造、整数シフト、
TR1〜TR4、Pretriangulated および S5〜S7 は未完了。

## S4：固定頂点上の恒等成分と cofiber 比較の二成分

固定頂点上の一般補題には quasicategory 仮定なし。cofiber と suspension の
短複体の比較への適用には Quasicategory、任意の HasZeroMorphisms、
IsCofiberSequence、および同じ始点の指定 SuspensionSquare を仮定する。
正確な公開型（Lean の出力）：

```lean
SerrePositivity.InfinityCategories.homotopyNatTrans_fixedVertex_arrow.{u} {A X : SSet.{u}}
  (U : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} A Δ[1]) X) (i : Quiver.Hom.{u, u + 1} Δ[0] A) (x : X _⦋0⦌)
  (hfix :
    Eq.{u + 1} (CategoryStruct.comp.{u, u + 1} (whiskerRight.{u, u + 1} i Δ[1]) U)
      (CategoryStruct.comp.{u, u + 1} (SemiCartesianMonoidalCategory.snd.{u, u + 1} Δ[0] Δ[1]) (const.{u} x))) :
  Eq.{u + 1}
    (Arrow.mk.{u, u}
      (NatTrans.app.{u, u, u, u} (SerrePositivity.InfinityCategories.homotopyNatTrans.{u} U)
        (HomotopyCategory.mk.{u} (SSet.yonedaEquiv.{u} i))))
    (Arrow.mk.{u, u} (CategoryStruct.id.{u, u} (HomotopyCategory.mk.{u} x)))
SerrePositivity.InfinityCategories.homotopyNatTransOfEndpoints_fixedVertex_arrow.{u} {A X : SSet.{u}}
  {F G : Quiver.Hom.{u, u + 1} A X} (U : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} A Δ[1]) X)
  (h₀ : Eq.{u + 1} (CategoryStruct.comp.{u, u + 1} ι₀.{u} U) F)
  (h₁ : Eq.{u + 1} (CategoryStruct.comp.{u, u + 1} ι₁.{u} U) G) (i : Quiver.Hom.{u, u + 1} Δ[0] A) (x : X _⦋0⦌)
  (hfix :
    Eq.{u + 1} (CategoryStruct.comp.{u, u + 1} (whiskerRight.{u, u + 1} i Δ[1]) U)
      (CategoryStruct.comp.{u, u + 1} (SemiCartesianMonoidalCategory.snd.{u, u + 1} Δ[0] Δ[1]) (const.{u} x))) :
  Eq.{u + 1}
    (Arrow.mk.{u, u}
      (NatTrans.app.{u, u, u, u} (SerrePositivity.InfinityCategories.homotopyNatTransOfEndpoints.{u} U h₀ h₁)
        (HomotopyCategory.mk.{u} (SSet.yonedaEquiv.{u} i))))
    (Arrow.mk.{u, u} (CategoryStruct.id.{u, u} (HomotopyCategory.mk.{u} x)))
SerrePositivity.InfinityCategories.cofiberSuspensionShortComplexMap_τ₁_arrow.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  [HasZeroMorphisms.{u, u} ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} X)]
  (t : SerrePositivity.InfinityCategories.ZeroTriangle.{u} X)
  (ht : SerrePositivity.InfinityCategories.IsCofiberSequence.{u} t)
  (s :
    SerrePositivity.InfinityCategories.SuspensionSquare.{u}
      (SerrePositivity.InfinityCategories.squareVertex.{u}
        (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} t) 0 0)) :
  Eq.{u + 1}
    (Arrow.mk.{u, u}
      (ShortComplex.Hom.τ₁.{u, u} (SerrePositivity.InfinityCategories.cofiberSuspensionShortComplexMap.{u} t ht s)))
    (Arrow.mk.{u, u}
      (CategoryStruct.id.{u, u}
        (ShortComplex.X₁.{u, u} (SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplex.{u} t))))
SerrePositivity.InfinityCategories.cofiberSuspensionShortComplexMap_τ₁_eqToHom.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  [HasZeroMorphisms.{u, u} ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} X)]
  (t : SerrePositivity.InfinityCategories.ZeroTriangle.{u} X)
  (ht : SerrePositivity.InfinityCategories.IsCofiberSequence.{u} t)
  (s :
    SerrePositivity.InfinityCategories.SuspensionSquare.{u}
      (SerrePositivity.InfinityCategories.squareVertex.{u}
        (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} t) 0 0)) :
  Eq.{u + 1}
    (ShortComplex.Hom.τ₁.{u, u} (SerrePositivity.InfinityCategories.cofiberSuspensionShortComplexMap.{u} t ht s))
    (eqToHom.{u, u} ⋯)
SerrePositivity.InfinityCategories.cofiberSuspensionShortComplexMap_τ₁_isIso.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  [HasZeroMorphisms.{u, u} ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} X)]
  (t : SerrePositivity.InfinityCategories.ZeroTriangle.{u} X)
  (ht : SerrePositivity.InfinityCategories.IsCofiberSequence.{u} t)
  (s :
    SerrePositivity.InfinityCategories.SuspensionSquare.{u}
      (SerrePositivity.InfinityCategories.squareVertex.{u}
        (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} t) 0 0)) :
  IsIso.{u, u}
    (ShortComplex.Hom.τ₁.{u, u} (SerrePositivity.InfinityCategories.cofiberSuspensionShortComplexMap.{u} t ht s))
SerrePositivity.InfinityCategories.cofiberSuspensionShortComplexMap_τ₂_eq_zero.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  [HasZeroMorphisms.{u, u} ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} X)]
  (t : SerrePositivity.InfinityCategories.ZeroTriangle.{u} X)
  (ht : SerrePositivity.InfinityCategories.IsCofiberSequence.{u} t)
  (s :
    SerrePositivity.InfinityCategories.SuspensionSquare.{u}
      (SerrePositivity.InfinityCategories.squareVertex.{u}
        (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} t) 0 0)) :
  Eq.{u + 1}
    (ShortComplex.Hom.τ₂.{u, u} (SerrePositivity.InfinityCategories.cofiberSuspensionShortComplexMap.{u} t ht s)) 0
```

対象 CofiberComparisonComponents ビルド 1993 jobs、Stable 集約ビルド 2065 jobs、
公開型の抽出、公理監査はすべて終了コード 0。監査は 120 モジュール・1150 宣言
（生成・非公開宣言を含む）について標準三公理のみ。`git diff --check` 成功。
接続射全体の選択独立性・自然性、Σf との零合成、前加法構造、整数シフト、
TR1〜TR4、Pretriangulated および S5〜S7 は未完了。

## S4：正次元境界からの充満忠実性と普遍余錐間の射の一意な持ち上げ

写像空間の境界持ち上げ・trivial Kan fibration 判定には元・値域の追加仮定なし。
IsFullyFaithful の一般判定と相対始対象の射影には元・値域の Quasicategory を仮定する。
普遍余錐への適用には X の Quasicategory のみ。全図式の余極限の存在は要求しない。
正確な公開型（Lean の出力）：

```lean
SerrePositivity.InfinityCategories.pinchedHomMap_boundary_of_boundary_succ.{u} {X Y : SSet.{u}}
  (p : Quiver.Hom.{u, u + 1} X Y) (x y : X _⦋0⦌) (n : ℕ)
  [HasLiftingProperty.{u, u + 1} (Subcomplex.ι.{u} ∂Δ[HAdd.hAdd.{0, 0, 0} n 1]) p] :
  HasLiftingProperty.{u, u + 1} (Subcomplex.ι.{u} ∂Δ[n]) (SerrePositivity.InfinityCategories.pinchedHomMap.{u} p x y)
SerrePositivity.InfinityCategories.pinchedHomMap_trivialKanFibration_of_boundary_succ.{u} {X Y : SSet.{u}}
  (p : Quiver.Hom.{u, u + 1} X Y)
  (hp : ∀ (n : ℕ), HasLiftingProperty.{u, u + 1} (Subcomplex.ι.{u} ∂Δ[HAdd.hAdd.{0, 0, 0} n 1]) p) (x y : X _⦋0⦌) :
  SerrePositivity.InfinityCategories.TrivialKanFibration.{u}
    (SerrePositivity.InfinityCategories.pinchedHomMap.{u} p x y)
SerrePositivity.InfinityCategories.isFullyFaithful_of_boundary_succ.{u} {X Y : SSet.{u}} [Quasicategory.{u} X]
  [Quasicategory.{u} Y] (p : Quiver.Hom.{u, u + 1} X Y)
  (hp : ∀ (n : ℕ), HasLiftingProperty.{u, u + 1} (Subcomplex.ι.{u} ∂Δ[HAdd.hAdd.{0, 0, 0} n 1]) p) :
  SerrePositivity.InfinityCategories.IsFullyFaithful.{u} p
SerrePositivity.InfinityCategories.relativeInitialProjection_isFullyFaithful.{u} {E B : SSet.{u}} [Quasicategory.{u} E]
  [Quasicategory.{u} B] (p : Quiver.Hom.{u, u + 1} E B) :
  SerrePositivity.InfinityCategories.IsFullyFaithful.{u}
    (SerrePositivity.InfinityCategories.relativeInitialProjection.{u} p)
SerrePositivity.InfinityCategories.colimitCoconeProjection_isFullyFaithful.{u} (K X : SSet.{u}) [Quasicategory.{u} X] :
  SerrePositivity.InfinityCategories.IsFullyFaithful.{u}
    (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u} K X)
SerrePositivity.InfinityCategories.colimitCoconeProjectionHoFullyFaithful.{u} (K X : SSet.{u}) [Quasicategory.{u} X] :
  Functor.FullyFaithful.{u, u, u, u}
    (Cat.Hom.toFunctor.{u, u}
      (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
        (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u} K X)))
SerrePositivity.InfinityCategories.colimitCoconeProjection_ho_map_injective.{u} {K X : SSet.{u}} [Quasicategory.{u} X]
  {a b : ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} (SerrePositivity.InfinityCategories.colimitCocones.{u} K X))}
  {f g : Quiver.Hom.{u, u} a b}
  (h :
    Eq.{u + 1}
      (CategoryTheory.Functor.map.{u, u, u, u}
        (Cat.Hom.toFunctor.{u, u}
          (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
            (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u} K X)))
        f)
      (CategoryTheory.Functor.map.{u, u, u, u}
        (Cat.Hom.toFunctor.{u, u}
          (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
            (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u} K X)))
        g)) :
  Eq.{u + 1} f g
SerrePositivity.InfinityCategories.colimitCoconeLiftHom.{u} {K X : SSet.{u}} [Quasicategory.{u} X]
  {a b : ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} (SerrePositivity.InfinityCategories.colimitCocones.{u} K X))}
  (f :
    Quiver.Hom.{u, u}
      (Functor.obj.{u, u, u, u}
        (Cat.Hom.toFunctor.{u, u}
          (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
            (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u} K X)))
        a)
      (Functor.obj.{u, u, u, u}
        (Cat.Hom.toFunctor.{u, u}
          (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
            (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u} K X)))
        b)) :
  Quiver.Hom.{u, u} a b
SerrePositivity.InfinityCategories.colimitCoconeProjection_map_liftHom.{u} {K X : SSet.{u}} [Quasicategory.{u} X]
  {a b : ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} (SerrePositivity.InfinityCategories.colimitCocones.{u} K X))}
  (f :
    Quiver.Hom.{u, u}
      (Functor.obj.{u, u, u, u}
        (Cat.Hom.toFunctor.{u, u}
          (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
            (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u} K X)))
        a)
      (Functor.obj.{u, u, u, u}
        (Cat.Hom.toFunctor.{u, u}
          (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
            (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u} K X)))
        b)) :
  Eq.{u + 1}
    (CategoryTheory.Functor.map.{u, u, u, u}
      (Cat.Hom.toFunctor.{u, u}
        (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
          (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u} K X)))
      (SerrePositivity.InfinityCategories.colimitCoconeLiftHom.{u} f))
    f
SerrePositivity.InfinityCategories.colimitCoconeLiftHom_unique.{u} {K X : SSet.{u}} [Quasicategory.{u} X]
  {a b : ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} (SerrePositivity.InfinityCategories.colimitCocones.{u} K X))}
  (f :
    Quiver.Hom.{u, u}
      (Functor.obj.{u, u, u, u}
        (Cat.Hom.toFunctor.{u, u}
          (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
            (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u} K X)))
        a)
      (Functor.obj.{u, u, u, u}
        (Cat.Hom.toFunctor.{u, u}
          (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
            (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u} K X)))
        b))
  (g : Quiver.Hom.{u, u} a b)
  (hg :
    Eq.{u + 1}
      (CategoryTheory.Functor.map.{u, u, u, u}
        (Cat.Hom.toFunctor.{u, u}
          (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
            (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u} K X)))
        g)
      f) :
  Eq.{u + 1} g (SerrePositivity.InfinityCategories.colimitCoconeLiftHom.{u} f)
SerrePositivity.InfinityCategories.colimitCoconeLiftHom_id.{u} {K X : SSet.{u}} [Quasicategory.{u} X]
  (a : ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} (SerrePositivity.InfinityCategories.colimitCocones.{u} K X))) :
  Eq.{u + 1}
    (SerrePositivity.InfinityCategories.colimitCoconeLiftHom.{u}
      (CategoryStruct.id.{u, u}
        (Functor.obj.{u, u, u, u}
          (Cat.Hom.toFunctor.{u, u}
            (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
              (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u} K X)))
          a)))
    (CategoryStruct.id.{u, u} a)
SerrePositivity.InfinityCategories.colimitCoconeLiftHom_comp.{u} {K X : SSet.{u}} [Quasicategory.{u} X]
  {a b c :
    ↑(Functor.obj.{u, u, u + 1, u + 1} hoFunctor.{u} (SerrePositivity.InfinityCategories.colimitCocones.{u} K X))}
  (f :
    Quiver.Hom.{u, u}
      (Functor.obj.{u, u, u, u}
        (Cat.Hom.toFunctor.{u, u}
          (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
            (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u} K X)))
        a)
      (Functor.obj.{u, u, u, u}
        (Cat.Hom.toFunctor.{u, u}
          (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
            (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u} K X)))
        b))
  (g :
    Quiver.Hom.{u, u}
      (Functor.obj.{u, u, u, u}
        (Cat.Hom.toFunctor.{u, u}
          (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
            (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u} K X)))
        b)
      (Functor.obj.{u, u, u, u}
        (Cat.Hom.toFunctor.{u, u}
          (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
            (SerrePositivity.InfinityCategories.colimitCoconeProjection.{u} K X)))
        c)) :
  Eq.{u + 1} (SerrePositivity.InfinityCategories.colimitCoconeLiftHom.{u} (CategoryStruct.comp.{u, u} f g))
    (CategoryStruct.comp.{u, u} (SerrePositivity.InfinityCategories.colimitCoconeLiftHom.{u} f)
      (SerrePositivity.InfinityCategories.colimitCoconeLiftHom.{u} g))
```

対象 ColimitHomLift ビルド 1973 jobs、Stable 集約ビルド 2068 jobs、
公開型抽出、公理監査はすべて終了コード 0。監査は 123 モジュール・1162 宣言
（生成・非公開宣言を含む）について標準三公理のみ。`git diff --check` 成功。
基底の h の射を固定した普遍余錐間の射の一意性・関手性まで完了。
接続射全体の選択独立性には span 比較自体の一意性が未完了。自然性、Σf との零合成、
前加法構造、整数シフト、TR1〜TR4、Pretriangulated および S5〜S7 も未完了。

## S4：終対象への相対境界充填と始点固定の span 比較の一意性

prism・辺・span の相対境界充填は、指定した最後の終点の終対象性のみを仮定し、
値域の Quasicategory は不要。相対終点への写像空間の trivial Kan fibration も
元・値域の Quasicategory は不要。h の Hom の全単射には元・値域 Quasicategory、
span の比較の一意性への適用には X が Quasicategory であることを仮定する。
正確な公開型（Lean の出力）：

```lean
SerrePositivity.InfinityCategories.stable_prism_extend_terminal_last.{u} {X : SSet.{u}} (n : ℕ)
  (H : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] (Subcomplex.toSSet.{u} ∂Δ[HAdd.hAdd.{0, 0, 0} n 1])) X)
  (F₀ : Quiver.Hom.{u, u + 1} Δ[HAdd.hAdd.{0, 0, 0} n 1] X)
  (hF₀ :
    Eq.{u + 1} (CategoryStruct.comp.{u, u + 1} (Subcomplex.ι.{u} ∂Δ[HAdd.hAdd.{0, 0, 0} n 1]) F₀)
      (CategoryStruct.comp.{u, u + 1}
        (SerrePositivity.InfinityCategories.prismEndpoint.{u} 0 (Subcomplex.toSSet.{u} ∂Δ[HAdd.hAdd.{0, 0, 0} n 1])) H))
  (ht :
    SerrePositivity.InfinityCategories.IsTerminalVertex.{u}
      ((ConcreteCategory.hom.{u, u, u + 1, u} (NatTrans.app.{0, u, 0, u + 1} H (Opposite.op.{1} ⦋0⦌)))
        (Prod.mk.{u, u} ((Equiv.symm.{u + 1, 1} stdSimplex.obj₀Equiv.{u}) 1)
          (Subtype.mk.{u + 1} ((Equiv.symm.{u + 1, 1} stdSimplex.obj₀Equiv.{u}) (Fin.last (HAdd.hAdd.{0, 0, 0} n 1)))
            ⋯)))) :
  ∃ F,
    Eq.{u + 1}
        (CategoryStruct.comp.{u, u + 1} (whiskerLeft.{u, u + 1} Δ[1] (Subcomplex.ι.{u} ∂Δ[HAdd.hAdd.{0, 0, 0} n 1])) F)
        H ∧
      Eq.{u + 1}
        (CategoryStruct.comp.{u, u + 1}
          (SerrePositivity.InfinityCategories.prismEndpoint.{u} 0 Δ[HAdd.hAdd.{0, 0, 0} n 1]) F)
        F₀
SerrePositivity.InfinityCategories.terminalBoundaryLifting_arrowSource_of_terminalTarget.{u} {X : SSet.{u}}
  (g : Quiver.Hom.{u, u + 1} Δ[1] X)
  (hg :
    SerrePositivity.InfinityCategories.IsTerminalVertex.{u}
      ((ConcreteCategory.hom.{u, u, u + 1, u} (NatTrans.app.{0, u, 0, u + 1} g (Opposite.op.{1} ⦋0⦌)))
        ((Equiv.symm.{u + 1, 1} stdSimplex.obj₀Equiv.{u}) 1))) :
  SerrePositivity.InfinityCategories.TerminalBoundaryLifting.{u}
    (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u} ((Equiv.symm.{u + 1, 1} stdSimplex.obj₀Equiv.{u}) 0))
    (SerrePositivity.InfinityCategories.functorVertex.{u} g)
SerrePositivity.InfinityCategories.spanSourceEvaluation.{u} (X : SSet.{u}) :
  Quiver.Hom.{u, u + 1} (Subcomplex.toSSet.{u} Λ[2, 0] ⟹ X) X
SerrePositivity.InfinityCategories.spanSourceEvaluation_right.{u} (X : SSet.{u}) :
  Eq.{u + 1}
    (CategoryStruct.comp.{u, u + 1} (NatTrans.app.{u, u, u + 1, u + 1} (pre.{u, u + 1} horn₂₀.ι₀₂.{u}) X)
      (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u} ((Equiv.symm.{u + 1, 1} stdSimplex.obj₀Equiv.{u}) 0)))
    (SerrePositivity.InfinityCategories.spanSourceEvaluation.{u} X)
SerrePositivity.InfinityCategories.terminalBoundaryLifting_spanSource_of_terminalTargets.{u} {X : SSet.{u}}
  (g : Quiver.Hom.{u, u + 1} (Subcomplex.toSSet.{u} Λ[2, 0]) X)
  (hg₁ :
    SerrePositivity.InfinityCategories.IsTerminalVertex.{u}
      ((ConcreteCategory.hom.{u, u, u + 1, u}
          (NatTrans.app.{0, u, 0, u + 1} (CategoryStruct.comp.{u, u + 1} horn₂₀.ι₀₁.{u} g) (Opposite.op.{1} ⦋0⦌)))
        ((Equiv.symm.{u + 1, 1} stdSimplex.obj₀Equiv.{u}) 1)))
  (hg₂ :
    SerrePositivity.InfinityCategories.IsTerminalVertex.{u}
      ((ConcreteCategory.hom.{u, u, u + 1, u}
          (NatTrans.app.{0, u, 0, u + 1} (CategoryStruct.comp.{u, u + 1} horn₂₀.ι₀₂.{u} g) (Opposite.op.{1} ⦋0⦌)))
        ((Equiv.symm.{u + 1, 1} stdSimplex.obj₀Equiv.{u}) 1))) :
  SerrePositivity.InfinityCategories.TerminalBoundaryLifting.{u}
    (SerrePositivity.InfinityCategories.spanSourceEvaluation.{u} X)
    (SerrePositivity.InfinityCategories.functorVertex.{u} g)
SerrePositivity.InfinityCategories.TerminalBoundaryLifting.exists_joinBoundary_lift.{u} {E B : SSet.{u}}
  {p : Quiver.Hom.{u, u + 1} E B} {y : E _⦋0⦌} (hy : SerrePositivity.InfinityCategories.TerminalBoundaryLifting.{u} p y)
  (n : ℕ) (B₀ : Subcomplex.{u} Δ[0]) (hB₀ : Eq.{u + 1} B₀ ∂Δ[0])
  (a : Quiver.Hom.{u, u + 1} (Subcomplex.toSSet.{u} (SerrePositivity.InfinityCategories.joinUnion.{u} ∂Δ[n] B₀)) E)
  (b : Quiver.Hom.{u, u + 1} (SerrePositivity.InfinityCategories.join.{u} Δ[n] Δ[0]) B)
  (hw :
    Eq.{u + 1} (CategoryStruct.comp.{u, u + 1} a p)
      (CategoryStruct.comp.{u, u + 1} (Subcomplex.ι.{u} (SerrePositivity.InfinityCategories.joinUnion.{u} ∂Δ[n] B₀)) b))
  (hlast :
    Eq.{u + 1}
      (CategoryStruct.comp.{u, u + 1}
        (SerrePositivity.InfinityCategories.joinInr.{u} (Subcomplex.toSSet.{u} ∂Δ[n]) Δ[0])
        (CategoryStruct.comp.{u, u + 1} (SerrePositivity.InfinityCategories.joinUnionLeft.{u} ∂Δ[n] B₀) a))
      ((Equiv.symm.{u + 1, u + 1} SSet.yonedaEquiv.{u}) y)) :
  ∃ F,
    Eq.{u + 1}
        (CategoryStruct.comp.{u, u + 1} (Subcomplex.ι.{u} (SerrePositivity.InfinityCategories.joinUnion.{u} ∂Δ[n] B₀))
          F)
        a ∧
      Eq.{u + 1} (CategoryStruct.comp.{u, u + 1} F p) b
SerrePositivity.InfinityCategories.pinchedHomMap_boundary_of_terminalBoundaryLifting.{u} {X Y : SSet.{u}}
  (p : Quiver.Hom.{u, u + 1} X Y) {y : X _⦋0⦌} (ht : SerrePositivity.InfinityCategories.TerminalBoundaryLifting.{u} p y)
  (x : X _⦋0⦌) (n : ℕ) :
  HasLiftingProperty.{u, u + 1} (Subcomplex.ι.{u} ∂Δ[n]) (SerrePositivity.InfinityCategories.pinchedHomMap.{u} p x y)
SerrePositivity.InfinityCategories.pinchedHomMap_trivialKanFibration_of_terminalBoundaryLifting.{u} {X Y : SSet.{u}}
  (p : Quiver.Hom.{u, u + 1} X Y) {y : X _⦋0⦌} (ht : SerrePositivity.InfinityCategories.TerminalBoundaryLifting.{u} p y)
  (x : X _⦋0⦌) :
  SerrePositivity.InfinityCategories.TrivialKanFibration.{u}
    (SerrePositivity.InfinityCategories.pinchedHomMap.{u} p x y)
SerrePositivity.InfinityCategories.homotopyCategoryMap_bijective_of_terminalBoundaryLifting.{u} {X Y : SSet.{u}}
  [Quasicategory.{u} X] [Quasicategory.{u} Y] (p : Quiver.Hom.{u, u + 1} X Y) {y : X _⦋0⦌}
  (ht : SerrePositivity.InfinityCategories.TerminalBoundaryLifting.{u} p y) (x : X _⦋0⦌) :
  Function.Bijective.{u + 1, u + 1}
    (CategoryTheory.Functor.map.{u, u, u, u}
      (Cat.Hom.toFunctor.{u, u} (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u} p)))
SerrePositivity.InfinityCategories.homotopyEvaluation_arrow.{u} {A X : SSet.{u}} {F G : Quiver.Hom.{u, u + 1} A X}
  (H : Homotopy.{u} F G) (a : A _⦋0⦌) :
  Eq.{u + 1}
    (Arrow.mk.{u, u}
      (CategoryTheory.Functor.map.{u, u, u, u}
        (Cat.Hom.toFunctor.{u, u}
          (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
            (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u} a)))
        (Truncated.HomotopyCategory.homMk.{u}
          (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u} H))))
    (Arrow.mk.{u, u}
      (NatTrans.app.{u, u, u, u}
        (SerrePositivity.InfinityCategories.homotopyNatTrans.{u} (RelativeMorphism.Homotopy.h.{u} H))
        (HomotopyCategory.mk.{u} a)))
SerrePositivity.InfinityCategories.homotopyEvaluation_eq_of_fixedVertex.{u} {A X : SSet.{u}}
  {F G : Quiver.Hom.{u, u + 1} A X} (H J : Homotopy.{u} F G) (i : Quiver.Hom.{u, u + 1} Δ[0] A) (x : X _⦋0⦌)
  (hH :
    Eq.{u + 1} (CategoryStruct.comp.{u, u + 1} (whiskerRight.{u, u + 1} i Δ[1]) (RelativeMorphism.Homotopy.h.{u} H))
      (CategoryStruct.comp.{u, u + 1} (SemiCartesianMonoidalCategory.snd.{u, u + 1} Δ[0] Δ[1]) (const.{u} x)))
  (hJ :
    Eq.{u + 1} (CategoryStruct.comp.{u, u + 1} (whiskerRight.{u, u + 1} i Δ[1]) (RelativeMorphism.Homotopy.h.{u} J))
      (CategoryStruct.comp.{u, u + 1} (SemiCartesianMonoidalCategory.snd.{u, u + 1} Δ[0] Δ[1]) (const.{u} x))) :
  Eq.{u + 1}
    (CategoryTheory.Functor.map.{u, u, u, u}
      (Cat.Hom.toFunctor.{u, u}
        (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
          (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u} (SSet.yonedaEquiv.{u} i))))
      (Truncated.HomotopyCategory.homMk.{u} (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u} H)))
    (CategoryTheory.Functor.map.{u, u, u, u}
      (Cat.Hom.toFunctor.{u, u}
        (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
          (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u} (SSet.yonedaEquiv.{u} i))))
      (Truncated.HomotopyCategory.homMk.{u} (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u} J)))
SerrePositivity.InfinityCategories.spanSourceEvaluation_homMap_bijective.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  (f g : Quiver.Hom.{u, u + 1} (Subcomplex.toSSet.{u} Λ[2, 0]) X)
  (hg₁ :
    SerrePositivity.InfinityCategories.IsTerminalVertex.{u}
      ((ConcreteCategory.hom.{u, u, u + 1, u}
          (NatTrans.app.{0, u, 0, u + 1} (CategoryStruct.comp.{u, u + 1} horn₂₀.ι₀₁.{u} g) (Opposite.op.{1} ⦋0⦌)))
        ((Equiv.symm.{u + 1, 1} stdSimplex.obj₀Equiv.{u}) 1)))
  (hg₂ :
    SerrePositivity.InfinityCategories.IsTerminalVertex.{u}
      ((ConcreteCategory.hom.{u, u, u + 1, u}
          (NatTrans.app.{0, u, 0, u + 1} (CategoryStruct.comp.{u, u + 1} horn₂₀.ι₀₂.{u} g) (Opposite.op.{1} ⦋0⦌)))
        ((Equiv.symm.{u + 1, 1} stdSimplex.obj₀Equiv.{u}) 1))) :
  Function.Bijective.{u + 1, u + 1}
    (CategoryTheory.Functor.map.{u, u, u, u}
      (Cat.Hom.toFunctor.{u, u}
        (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
          (SerrePositivity.InfinityCategories.spanSourceEvaluation.{u} X))))
SerrePositivity.InfinityCategories.suspensionSpan_hom_ext.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]) X)
  (s :
    SerrePositivity.InfinityCategories.SuspensionSquare.{u} (SerrePositivity.InfinityCategories.squareVertex.{u} F 0 0))
  {a b :
    Quiver.Hom.{u, u}
      (HomotopyCategory.mk.{u}
        (SerrePositivity.InfinityCategories.functorVertex.{u} (SerrePositivity.InfinityCategories.pushoutSpan.{u} F)))
      (HomotopyCategory.mk.{u}
        (SerrePositivity.InfinityCategories.functorVertex.{u}
          (SerrePositivity.InfinityCategories.pushoutSpan.{u}
            (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u}
              (SerrePositivity.InfinityCategories.SuspensionSquare.toZeroTriangle.{u} s)))))}
  (h :
    Eq.{u + 1}
      (CategoryTheory.Functor.map.{u, u, u, u}
        (Cat.Hom.toFunctor.{u, u}
          (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
            (SerrePositivity.InfinityCategories.spanSourceEvaluation.{u} X)))
        a)
      (CategoryTheory.Functor.map.{u, u, u, u}
        (Cat.Hom.toFunctor.{u, u}
          (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} hoFunctor.{u}
            (SerrePositivity.InfinityCategories.spanSourceEvaluation.{u} X)))
        b)) :
  Eq.{u + 1} a b
SerrePositivity.InfinityCategories.spanSourceEvaluation_eq_evaluate.{u} (X : SSet.{u}) :
  Eq.{u + 1} (SerrePositivity.InfinityCategories.spanSourceEvaluation.{u} X)
    (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u}
      (SSet.yonedaEquiv.{u}
        (CategoryStruct.comp.{u, u + 1} (CosimplicialObject.δ.{u, u + 1} stdSimplex.{u} 1) horn₂₀.ι₀₁.{u})))
SerrePositivity.InfinityCategories.suspensionSpanHomotopy_homMk_eq.{u} {X : SSet.{u}} [Quasicategory.{u} X]
  (F : Quiver.Hom.{u, u + 1} (tensorObj.{u, u + 1} Δ[1] Δ[1]) X)
  (s :
    SerrePositivity.InfinityCategories.SuspensionSquare.{u} (SerrePositivity.InfinityCategories.squareVertex.{u} F 0 0))
  (H J :
    Homotopy.{u} (SerrePositivity.InfinityCategories.pushoutSpan.{u} F)
      (SerrePositivity.InfinityCategories.pushoutSpan.{u}
        (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u}
          (SerrePositivity.InfinityCategories.SuspensionSquare.toZeroTriangle.{u} s))))
  (hH :
    Eq.{u + 1}
      (CategoryStruct.comp.{u, u + 1}
        (whiskerRight.{u, u + 1}
          (CategoryStruct.comp.{u, u + 1} (CosimplicialObject.δ.{u, u + 1} stdSimplex.{u} 1) horn₂₀.ι₀₁.{u}) Δ[1])
        (RelativeMorphism.Homotopy.h.{u} H))
      (CategoryStruct.comp.{u, u + 1} (SemiCartesianMonoidalCategory.snd.{u, u + 1} Δ[0] Δ[1])
        (const.{u} (SerrePositivity.InfinityCategories.squareVertex.{u} F 0 0))))
  (hJ :
    Eq.{u + 1}
      (CategoryStruct.comp.{u, u + 1}
        (whiskerRight.{u, u + 1}
          (CategoryStruct.comp.{u, u + 1} (CosimplicialObject.δ.{u, u + 1} stdSimplex.{u} 1) horn₂₀.ι₀₁.{u}) Δ[1])
        (RelativeMorphism.Homotopy.h.{u} J))
      (CategoryStruct.comp.{u, u + 1} (SemiCartesianMonoidalCategory.snd.{u, u + 1} Δ[0] Δ[1])
        (const.{u} (SerrePositivity.InfinityCategories.squareVertex.{u} F 0 0)))) :
  Eq.{u + 1}
    (Truncated.HomotopyCategory.homMk.{u} (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u} H))
    (Truncated.HomotopyCategory.homMk.{u} (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u} J))
```

対象 SpanComparisonUniqueness ビルド 1992 jobs、Stable 集約ビルド 2075 jobs、
公開型抽出、公理監査はすべて終了コード 0。監査は 130 モジュール・1181 宣言
（生成・非公開宣言を含む）について標準三公理のみ。`git diff --check` 成功。
始点固定の suspension span 比較の h の射の一意性まで完了。接続射全体の選択独立性は、
これと前回の普遍余錐間の持ち上げの一意性を、頂点で取り出した射に照合する段階が未完了。
自然性、Σf との零合成、前加法構造、整数シフト、TR1〜TR4、Pretriangulated、S5〜S7 も未完了。


## 指定 suspension への接続射の比較ホモトピーに関する選択独立性

普遍余錐の射影の忠実性と、始点固定の span 比較の一意性を四角形で照合した。
指定した suspension 四角形を固定したとき、任意の始点固定の比較ホモトピーの
第三成分が `cofiberConnectingToSuspension` に一致する。
主な前提は X の Quasicategory 性、元の列の IsCofiberSequence、h X の
HasZeroMorphisms。四角形の比較の一意性自体には零射構造は不要。
以下は Lean による公開宣言の正確な型の出力（宇宙・完全修飾名つき）。

```text
SerrePositivity.InfinityCategories.exists_fullSubcomplexEdgeLift.{u} {X : SSet.{u}}
  (P : CategoryTheory.Functor.obj.{0, u, 0, u + 1} X (Opposite.op.{1} { len := 0 }) → Prop)
  (a b :
    CategoryTheory.Functor.obj.{0, u, 0, u + 1}
      (SSet.Subcomplex.toSSet.{u} (SerrePositivity.InfinityCategories.fullSubcomplexOnVertices.{u} X P))
      (Opposite.op.{1} { len := 0 }))
  (e : SSet.Truncated.Edge.{u} ↑a ↑b) :
  ∃ f,
    Eq.{u + 1}
      (SSet.Truncated.Edge.map.{u} f
        (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} (SSet.truncation.{u} 2)
          (SSet.Subcomplex.ι.{u} (SerrePositivity.InfinityCategories.fullSubcomplexOnVertices.{u} X P))))
      e
SerrePositivity.InfinityCategories.colimitCoconeHomotopyEdge.{u} {K X : SSet.{u}} [SSet.Quasicategory.{u} X]
  {p q : Quiver.Hom.{u, u + 1} K X} (c : SerrePositivity.InfinityCategories.JoinCocone.{u} p)
  (d : SerrePositivity.InfinityCategories.JoinCocone.{u} q)
  (hc : SerrePositivity.InfinityCategories.IsColimitCone.{u} c)
  (hd : SerrePositivity.InfinityCategories.IsColimitCone.{u} d) (H : SSet.Homotopy.{u} ↑c ↑d) :
  SSet.Truncated.Edge.{u} (SerrePositivity.InfinityCategories.colimitCoconeVertex.{u} c hc)
    (SerrePositivity.InfinityCategories.colimitCoconeVertex.{u} d hd)
SerrePositivity.InfinityCategories.colimitCoconeHomotopyEdge_map.{u} {K X : SSet.{u}} [SSet.Quasicategory.{u} X]
  {p q : Quiver.Hom.{u, u + 1} K X} (c : SerrePositivity.InfinityCategories.JoinCocone.{u} p)
  (d : SerrePositivity.InfinityCategories.JoinCocone.{u} q)
  (hc : SerrePositivity.InfinityCategories.IsColimitCone.{u} c)
  (hd : SerrePositivity.InfinityCategories.IsColimitCone.{u} d) (H : SSet.Homotopy.{u} ↑c ↑d) :
  Eq.{u + 1}
    (SSet.Truncated.Edge.map.{u} (SerrePositivity.InfinityCategories.colimitCoconeHomotopyEdge.{u} c d hc hd H)
      (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} (SSet.truncation.{u} 2)
        (SSet.Subcomplex.ι.{u}
          (SerrePositivity.InfinityCategories.relativeInitialVertices.{u}
            (SerrePositivity.InfinityCategories.coconeRestriction.{u} K X)))))
    (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u} H)
SerrePositivity.InfinityCategories.colimitCoconeHomotopy_homMk_eq.{u} {K X : SSet.{u}} [SSet.Quasicategory.{u} X]
  {p q : Quiver.Hom.{u, u + 1} K X} (c : SerrePositivity.InfinityCategories.JoinCocone.{u} p)
  (d : SerrePositivity.InfinityCategories.JoinCocone.{u} q)
  (hc : SerrePositivity.InfinityCategories.IsColimitCone.{u} c)
  (hd : SerrePositivity.InfinityCategories.IsColimitCone.{u} d) (H J : SSet.Homotopy.{u} ↑c ↑d)
  (h :
    Eq.{u + 1}
      (CategoryTheory.Functor.map.{u, u, u, u}
        (CategoryTheory.Cat.Hom.toFunctor.{u, u}
          (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} SSet.hoFunctor.{u}
            (SerrePositivity.InfinityCategories.coconeRestriction.{u} K X)))
        (SSet.Truncated.HomotopyCategory.homMk.{u}
          (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u} H)))
      (CategoryTheory.Functor.map.{u, u, u, u}
        (CategoryTheory.Cat.Hom.toFunctor.{u, u}
          (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} SSet.hoFunctor.{u}
            (SerrePositivity.InfinityCategories.coconeRestriction.{u} K X)))
        (SSet.Truncated.HomotopyCategory.homMk.{u}
          (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u} J)))) :
  Eq.{u + 1}
    (SSet.Truncated.HomotopyCategory.homMk.{u}
      (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u} H))
    (SSet.Truncated.HomotopyCategory.homMk.{u}
      (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u} J))
SerrePositivity.InfinityCategories.stableHomotopyPrecomp.{u} {A B X : SSet.{u}} (i : Quiver.Hom.{u, u + 1} A B)
  {F G : Quiver.Hom.{u, u + 1} B X} (H : SSet.Homotopy.{u} F G) :
  SSet.Homotopy.{u} (CategoryTheory.CategoryStruct.comp.{u, u + 1} i F)
    (CategoryTheory.CategoryStruct.comp.{u, u + 1} i G)
SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy_precomp.{u} {A B X : SSet.{u}}
  (i : Quiver.Hom.{u, u + 1} A B) {F G : Quiver.Hom.{u, u + 1} B X} (H : SSet.Homotopy.{u} F G) :
  Eq.{u + 1}
    (SSet.Truncated.Edge.map.{u} (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u} H)
      (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} (SSet.truncation.{u} 2)
        (CategoryTheory.NatTrans.app.{u, u, u + 1, u + 1} (CategoryTheory.MonoidalClosed.pre.{u, u + 1} i) X)))
    (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u}
      (SerrePositivity.InfinityCategories.stableHomotopyPrecomp.{u} i H))
SerrePositivity.InfinityCategories.homMk_functorEdge_precomp.{u} {A B X : SSet.{u}} (i : Quiver.Hom.{u, u + 1} A B)
  {F G : Quiver.Hom.{u, u + 1} B X} (H : SSet.Homotopy.{u} F G) :
  Eq.{u + 1}
    (CategoryTheory.Functor.map.{u, u, u, u}
      (CategoryTheory.Cat.Hom.toFunctor.{u, u}
        (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} SSet.hoFunctor.{u}
          (CategoryTheory.NatTrans.app.{u, u, u + 1, u + 1} (CategoryTheory.MonoidalClosed.pre.{u, u + 1} i) X)))
      (SSet.Truncated.HomotopyCategory.homMk.{u}
        (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u} H)))
    (SSet.Truncated.HomotopyCategory.homMk.{u}
      (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u}
        (SerrePositivity.InfinityCategories.stableHomotopyPrecomp.{u} i H)))
SerrePositivity.InfinityCategories.homMk_functorEdge_precomp_inv_hom_arrow.{u} {A B X : SSet.{u}}
  (e : CategoryTheory.Iso.{u, u + 1} A B) {F G : Quiver.Hom.{u, u + 1} B X} (H : SSet.Homotopy.{u} F G) :
  Eq.{u + 1}
    (CategoryTheory.Arrow.mk.{u, u}
      (SSet.Truncated.HomotopyCategory.homMk.{u}
        (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u}
          (SerrePositivity.InfinityCategories.stableHomotopyPrecomp.{u} (CategoryTheory.Iso.inv.{u, u + 1} e)
            (SerrePositivity.InfinityCategories.stableHomotopyPrecomp.{u} (CategoryTheory.Iso.hom.{u, u + 1} e) H)))))
    (CategoryTheory.Arrow.mk.{u, u}
      (SSet.Truncated.HomotopyCategory.homMk.{u}
        (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u} H)))
SerrePositivity.InfinityCategories.stableHomotopyPrecomp_span_source.{u} {X : SSet.{u}}
  {F G :
    Quiver.Hom.{u, u + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u, u + 1}
        (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 1 })
        (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 1 }))
      X}
  (H : SSet.Homotopy.{u} F G)
  (hH :
    Eq.{u + 1}
      (CategoryTheory.CategoryStruct.comp.{u, u + 1}
        (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u, u + 1}
          (CategoryTheory.CategoryStruct.comp.{u, u + 1}
            (CategoryTheory.CosimplicialObject.δ.{u, u + 1} SSet.stdSimplex.{u} 1)
            SerrePositivity.InfinityCategories.squareBottomEdge.{u})
          (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 1 }))
        (SSet.RelativeMorphism.Homotopy.h.{u} H))
      (CategoryTheory.CategoryStruct.comp.{u, u + 1}
        (CategoryTheory.SemiCartesianMonoidalCategory.snd.{u, u + 1}
          (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 0 })
          (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 1 }))
        (SSet.const.{u} (SerrePositivity.InfinityCategories.squareVertex.{u} F 0 0)))) :
  Eq.{u + 1}
    (CategoryTheory.CategoryStruct.comp.{u, u + 1}
      (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u, u + 1}
        (CategoryTheory.CategoryStruct.comp.{u, u + 1}
          (CategoryTheory.CosimplicialObject.δ.{u, u + 1} SSet.stdSimplex.{u} 1) SSet.horn₂₀.ι₀₁.{u})
        (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 1 }))
      (SSet.RelativeMorphism.Homotopy.h.{u}
        (SerrePositivity.InfinityCategories.stableHomotopyPrecomp.{u}
          SerrePositivity.InfinityCategories.spanSquareBoundary.{u} H)))
    (CategoryTheory.CategoryStruct.comp.{u, u + 1}
      (CategoryTheory.SemiCartesianMonoidalCategory.snd.{u, u + 1}
        (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 0 })
        (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 1 }))
      (SSet.const.{u} (SerrePositivity.InfinityCategories.squareVertex.{u} F 0 0)))
SerrePositivity.InfinityCategories.cofiberComparison_coconeRestriction.{u} {X : SSet.{u}}
  {F G :
    Quiver.Hom.{u, u + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u, u + 1}
        (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 1 })
        (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 1 }))
      X}
  (H : SSet.Homotopy.{u} F G) :
  Eq.{u + 1}
    (CategoryTheory.Functor.map.{u, u, u, u}
      (CategoryTheory.Cat.Hom.toFunctor.{u, u}
        (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} SSet.hoFunctor.{u}
          (SerrePositivity.InfinityCategories.coconeRestriction.{u} (SSet.Subcomplex.toSSet.{u} (SSet.horn.{u} 2 0))
            X)))
      (SSet.Truncated.HomotopyCategory.homMk.{u}
        (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u}
          (SerrePositivity.InfinityCategories.stableHomotopyPrecomp.{u}
            (CategoryTheory.Iso.hom.{u, u + 1} SerrePositivity.InfinityCategories.spanCoconeSquareIso.{u}) H))))
    (SSet.Truncated.HomotopyCategory.homMk.{u}
      (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u}
        (SerrePositivity.InfinityCategories.stableHomotopyPrecomp.{u}
          SerrePositivity.InfinityCategories.spanSquareBoundary.{u} H)))
SerrePositivity.InfinityCategories.cofiberSuspensionComparison_homMk_eq.{u} {X : SSet.{u}} [SSet.Quasicategory.{u} X]
  (F :
    Quiver.Hom.{u, u + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u, u + 1}
        (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 1 })
        (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 1 }))
      X)
  (hF : SerrePositivity.InfinityCategories.IsPushoutSquare.{u} F)
  (s :
    SerrePositivity.InfinityCategories.SuspensionSquare.{u} (SerrePositivity.InfinityCategories.squareVertex.{u} F 0 0))
  (H J :
    SSet.Homotopy.{u} F
      (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u}
        (SerrePositivity.InfinityCategories.SuspensionSquare.toZeroTriangle.{u} s)))
  (hH :
    Eq.{u + 1}
      (CategoryTheory.CategoryStruct.comp.{u, u + 1}
        (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u, u + 1}
          (CategoryTheory.CategoryStruct.comp.{u, u + 1}
            (CategoryTheory.CosimplicialObject.δ.{u, u + 1} SSet.stdSimplex.{u} 1)
            SerrePositivity.InfinityCategories.squareBottomEdge.{u})
          (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 1 }))
        (SSet.RelativeMorphism.Homotopy.h.{u} H))
      (CategoryTheory.CategoryStruct.comp.{u, u + 1}
        (CategoryTheory.SemiCartesianMonoidalCategory.snd.{u, u + 1}
          (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 0 })
          (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 1 }))
        (SSet.const.{u} (SerrePositivity.InfinityCategories.squareVertex.{u} F 0 0))))
  (hJ :
    Eq.{u + 1}
      (CategoryTheory.CategoryStruct.comp.{u, u + 1}
        (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u, u + 1}
          (CategoryTheory.CategoryStruct.comp.{u, u + 1}
            (CategoryTheory.CosimplicialObject.δ.{u, u + 1} SSet.stdSimplex.{u} 1)
            SerrePositivity.InfinityCategories.squareBottomEdge.{u})
          (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 1 }))
        (SSet.RelativeMorphism.Homotopy.h.{u} J))
      (CategoryTheory.CategoryStruct.comp.{u, u + 1}
        (CategoryTheory.SemiCartesianMonoidalCategory.snd.{u, u + 1}
          (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 0 })
          (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 1 }))
        (SSet.const.{u} (SerrePositivity.InfinityCategories.squareVertex.{u} F 0 0)))) :
  Eq.{u + 1}
    (SSet.Truncated.HomotopyCategory.homMk.{u}
      (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u} H))
    (SSet.Truncated.HomotopyCategory.homMk.{u}
      (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u} J))
SerrePositivity.InfinityCategories.cofiberComparison_τ₃_eq_of_source_fixed.{u} {X : SSet.{u}} [SSet.Quasicategory.{u} X]
  [CategoryTheory.Limits.HasZeroMorphisms.{u, u}
      ↑(CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} SSet.hoFunctor.{u} X)]
  (t : SerrePositivity.InfinityCategories.ZeroTriangle.{u} X)
  (ht : SerrePositivity.InfinityCategories.IsCofiberSequence.{u} t)
  (s :
    SerrePositivity.InfinityCategories.SuspensionSquare.{u}
      (SerrePositivity.InfinityCategories.squareVertex.{u}
        (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} t) 0 0))
  (H J :
    SSet.Homotopy.{u} (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} t)
      (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u}
        (SerrePositivity.InfinityCategories.SuspensionSquare.toZeroTriangle.{u} s)))
  (hH :
    Eq.{u + 1}
      (CategoryTheory.CategoryStruct.comp.{u, u + 1}
        (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u, u + 1}
          (CategoryTheory.CategoryStruct.comp.{u, u + 1}
            (CategoryTheory.CosimplicialObject.δ.{u, u + 1} SSet.stdSimplex.{u} 1)
            SerrePositivity.InfinityCategories.squareBottomEdge.{u})
          (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 1 }))
        (SSet.RelativeMorphism.Homotopy.h.{u} H))
      (CategoryTheory.CategoryStruct.comp.{u, u + 1}
        (CategoryTheory.SemiCartesianMonoidalCategory.snd.{u, u + 1}
          (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 0 })
          (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 1 }))
        (SSet.const.{u}
          (SerrePositivity.InfinityCategories.squareVertex.{u}
            (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} t) 0 0))))
  (hJ :
    Eq.{u + 1}
      (CategoryTheory.CategoryStruct.comp.{u, u + 1}
        (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u, u + 1}
          (CategoryTheory.CategoryStruct.comp.{u, u + 1}
            (CategoryTheory.CosimplicialObject.δ.{u, u + 1} SSet.stdSimplex.{u} 1)
            SerrePositivity.InfinityCategories.squareBottomEdge.{u})
          (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 1 }))
        (SSet.RelativeMorphism.Homotopy.h.{u} J))
      (CategoryTheory.CategoryStruct.comp.{u, u + 1}
        (CategoryTheory.SemiCartesianMonoidalCategory.snd.{u, u + 1}
          (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 0 })
          (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 1 }))
        (SSet.const.{u}
          (SerrePositivity.InfinityCategories.squareVertex.{u}
            (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} t) 0 0)))) :
  Eq.{u + 1}
    (CategoryTheory.ShortComplex.Hom.τ₃.{u, u}
      (SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplexMapOfHomotopy.{u} t
        (SerrePositivity.InfinityCategories.SuspensionSquare.toZeroTriangle.{u} s)
        (SSet.RelativeMorphism.Homotopy.h.{u} H) ⋯ ⋯))
    (CategoryTheory.ShortComplex.Hom.τ₃.{u, u}
      (SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplexMapOfHomotopy.{u} t
        (SerrePositivity.InfinityCategories.SuspensionSquare.toZeroTriangle.{u} s)
        (SSet.RelativeMorphism.Homotopy.h.{u} J) ⋯ ⋯))
SerrePositivity.InfinityCategories.cofiberComparison_τ₃_eq_connectingToSuspension.{u} {X : SSet.{u}}
  [SSet.Quasicategory.{u} X]
  [CategoryTheory.Limits.HasZeroMorphisms.{u, u}
      ↑(CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} SSet.hoFunctor.{u} X)]
  (t : SerrePositivity.InfinityCategories.ZeroTriangle.{u} X)
  (ht : SerrePositivity.InfinityCategories.IsCofiberSequence.{u} t)
  (s :
    SerrePositivity.InfinityCategories.SuspensionSquare.{u}
      (SerrePositivity.InfinityCategories.squareVertex.{u}
        (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} t) 0 0))
  (H :
    SSet.Homotopy.{u} (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} t)
      (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u}
        (SerrePositivity.InfinityCategories.SuspensionSquare.toZeroTriangle.{u} s)))
  (hH :
    Eq.{u + 1}
      (CategoryTheory.CategoryStruct.comp.{u, u + 1}
        (CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u, u + 1}
          (CategoryTheory.CategoryStruct.comp.{u, u + 1}
            (CategoryTheory.CosimplicialObject.δ.{u, u + 1} SSet.stdSimplex.{u} 1)
            SerrePositivity.InfinityCategories.squareBottomEdge.{u})
          (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 1 }))
        (SSet.RelativeMorphism.Homotopy.h.{u} H))
      (CategoryTheory.CategoryStruct.comp.{u, u + 1}
        (CategoryTheory.SemiCartesianMonoidalCategory.snd.{u, u + 1}
          (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 0 })
          (CategoryTheory.Functor.obj.{0, u, 0, u + 1} SSet.stdSimplex.{u} { len := 1 }))
        (SSet.const.{u}
          (SerrePositivity.InfinityCategories.squareVertex.{u}
            (SerrePositivity.InfinityCategories.ZeroTriangle.square.{u} t) 0 0)))) :
  Eq.{u + 1}
    (CategoryTheory.ShortComplex.Hom.τ₃.{u, u}
      (SerrePositivity.InfinityCategories.ZeroTriangle.hoShortComplexMapOfHomotopy.{u} t
        (SerrePositivity.InfinityCategories.SuspensionSquare.toZeroTriangle.{u} s)
        (SSet.RelativeMorphism.Homotopy.h.{u} H) ⋯ ⋯))
    (SerrePositivity.InfinityCategories.cofiberConnectingToSuspension.{u} t ht s)
SerrePositivity.InfinityCategories.homotopyEvaluationOfEndpoints_arrow.{u} {A X : SSet.{u}}
  {F G : Quiver.Hom.{u, u + 1} A X} (H : SSet.Homotopy.{u} F G)
  (a : CategoryTheory.Functor.obj.{0, u, 0, u + 1} A (Opposite.op.{1} { len := 0 })) :
  Eq.{u + 1}
    (CategoryTheory.Arrow.mk.{u, u}
      (CategoryTheory.Functor.map.{u, u, u, u}
        (CategoryTheory.Cat.Hom.toFunctor.{u, u}
          (CategoryTheory.Functor.map.{u, u, u + 1, u + 1} SSet.hoFunctor.{u}
            (SerrePositivity.InfinityCategories.evaluateFunctorAt.{u} a)))
        (SSet.Truncated.HomotopyCategory.homMk.{u}
          (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u} H))))
    (CategoryTheory.Arrow.mk.{u, u}
      (CategoryTheory.NatTrans.app.{u, u, u, u}
        (SerrePositivity.InfinityCategories.homotopyNatTransOfEndpoints.{u} (SSet.RelativeMorphism.Homotopy.h.{u} H) ⋯
          ⋯)
        (SSet.HomotopyCategory.mk.{u} a)))
```

対象 CofiberConnectingIndependence ビルド 2006 jobs、対象・Stable 集約ビルド
2080 jobs、公開型抽出、公理監査はすべて終了コード 0。監査は 135 モジュール・1199 宣言
（生成・非公開宣言を含む）について標準三公理のみ。`git diff --check` 成功。
指定 suspension を固定した比較ホモトピーの選択独立性まで完了。
suspension 四角形そのものの変更との整合、接続射の自然性、Σf との零合成、
前加法構造、整数シフト、TR1〜TR4、Pretriangulated、S5〜S7 は未完了。
