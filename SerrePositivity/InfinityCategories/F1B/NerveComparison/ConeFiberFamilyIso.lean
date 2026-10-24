module

public import SerrePositivity.InfinityCategories.F1B.NerveComparison.ConeRestrictionIso
public import SerrePositivity.InfinityCategories.F1B.Fibrations.VertexFiberSquareIso

/-!
概要：通常の錐と native な錐の族の比較を構成する。
方針：指数比較と固定図式上の fiber の同型を使う。
規約：同じ宇宙の小さい圏を扱う。
使われ方：B5 の局所極限の双方向比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet MonoidalClosed
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}

/-- 概要：指数比較は指定図式の頂点を保つ。
方針：指数比較と fiber の同型の射影公式を使う。
規約：同じ宇宙で元の指定図式と錐を保持する。
使われ方：B5 の局所極限と pointwise Kan の古典比較。 -/
lemma nerveConeRestriction_vertex : (SerrePositivity.InfinityCategories.F1B.nerveFunctorCategoryIso I C).hom.app (Opposite.op ⦋0⦌)
    (nerveVertex F) = functorVertex (nerveMap F) := SerrePositivity.InfinityCategories.F1B.nerveFunctorCategoryIso_vertex F
/-- 概要：通常の制限の nerve の fiber と native な錐の族を同型にする。
方針：指数比較と fiber の同型の射影公式を使う。
規約：同じ宇宙で元の指定図式と錐を保持する。
使われ方：B5 の局所極限と pointwise Kan の古典比較。 -/
def nerveConeFiberFamilyIso : vertexFiber
    (nerveMap (SerrePositivity.InfinityCategories.F1B.coneRestrictionFunctor (I := I) (C := C))) (nerveVertex F) ≅
      coneFamily (nerveMap F) :=
  SerrePositivity.InfinityCategories.F1B.vertexFiberSquareIso _ _ SerrePositivity.InfinityCategories.F1B.nerveConeExtensionIso (SerrePositivity.InfinityCategories.F1B.nerveFunctorCategoryIso I C)
    SerrePositivity.InfinityCategories.F1B.nerveConeRestriction_square
    (nerveVertex F) ≪≫ eqToIso (congrArg (vertexFiber (coneRestriction (nerve I) (nerve C)))
      (nerveConeRestriction_vertex (F := F)))
/-- 概要：錐の族の同型は拡張関手への包含を保つ。
方針：指数比較と fiber の同型の射影公式を使う。
規約：同じ宇宙で元の指定図式と錐を保持する。
使われ方：B5 の局所極限と pointwise Kan の古典比較。 -/
lemma nerveConeFiberFamilyIso_inclusion : (nerveConeFiberFamilyIso (F := F)).hom ≫
    vertexFiberι (coneRestriction (nerve I) (nerve C)) (functorVertex (nerveMap F)) =
      vertexFiberι (nerveMap (SerrePositivity.InfinityCategories.F1B.coneRestrictionFunctor (I := I) (C := C))) (nerveVertex F) ≫
        (SerrePositivity.InfinityCategories.F1B.nerveConeExtensionIso (I := I) (C := C)).hom := by
  dsimp only [nerveConeFiberFamilyIso]
  rw [Iso.trans_hom, Category.assoc, SerrePositivity.InfinityCategories.F1B.vertexFiberι_eqTransport (coneRestriction _ _)
    (nerveConeRestriction_vertex (F := F))]
  exact SerrePositivity.InfinityCategories.F1B.vertexFiberSquareIso_hom_inclusion _ _ _ _ _ _

end SerrePositivity.InfinityCategories.F1B
