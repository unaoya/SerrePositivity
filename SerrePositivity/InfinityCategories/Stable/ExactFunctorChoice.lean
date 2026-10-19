module
public import SerrePositivity.InfinityCategories.Stable.ExactFunctor
public import SerrePositivity.InfinityCategories.Stable.CofiberSquareComparisonIso
public import SerrePositivity.InfinityCategories.Stable.SquareFunctorTransport

/-! # cofiber の選択と関手同型による完全性の判定

概要：各辺で一つの cofiber の保存から完全性を得て、実関手同型で輸送する。
方針：同じ実辺の cofiber 四角形の比較同型と全四角形の普遍性の輸送を使う。
規約：両端は quasicategory、安定性は不要。使われ方：dg 部分圏の包含と Yoneda 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]

/-- 各実辺に一つ、像が押し出しになる cofiber があれば、零保存関手は完全。 -/
lemma isExactFunctor_of_preserves_chosen_cofibers (F : X ⟶ Y)
    (hF : PreservesZeroVertices F)
    (h : ∀ {x y : X _⦋0⦌} (e : Truncated.Edge (X := (truncation 2).obj X) x y),
      ∃ s : CofiberSquare e, IsPushoutSquare (s.square ≫ F)) : IsExactFunctor F where
  preservesZero := hF
  preservesCofiber t ht := by
    let f := edgeOfSimplex (SSet.yonedaEquiv (squareBottomEdge ≫ t.square))
    let s : CofiberSquare f := {
      toZeroTriangle := t
      bottom_edge := (SSet.yonedaEquiv.symm_apply_apply _).symm
      isPushout := ht }
    obtain ⟨r, hr⟩ := h f
    obtain ⟨e⟩ := nonempty_cofiberSquareFunctorIso r s
    exact hr.of_functorIso (e.postcomp F)

/-- 実関手圏の同型は、零頂点と cofiber 列の保存を輸送する。 -/
lemma isExactFunctor_of_functorIso {F G : X ⟶ Y} (e : FunctorIso F G)
    [IsExactFunctor F] : IsExactFunctor G where
  preservesZero x hx :=
    (IsExactFunctor.preservesZero (F := F) x hx).of_vertexIso (FunctorIso.app e x)
  preservesCofiber t ht :=
    (IsExactFunctor.preservesCofiber (F := F) t ht).of_functorIso (e.precomp t.square)

end SerrePositivity.InfinityCategories
