module

public import SerrePositivity.InfinityCategories.F1B.KanSliceDiagramIso
public import SerrePositivity.InfinityCategories.F1B.KanNerveConeEquiv
public import SerrePositivity.InfinityCategories.F1B.KanNerveOppositeIso

/-!
概要：通常の余錐と nerve の余錐を反転によって比較する。
方針：反対圏の nerve の同型と slice の同型を合成する。
規約：図式・余錐・頂点を固定し、同じ宇宙の小さい圏を扱う。
使われ方：B5 の局所余極限と pointwise Kan の古典比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}

/-- 概要：反対圏の nerve の slice と反転図式の slice を同型にする。
方針：反転と図式同型の射影公式を使う。
規約：指定した元の図式と余錐を保持する。
使われ方：B5 の局所余極限の双方向比較。 -/
def kanNerveOppositeSliceIso :
    sliceOver (nerveMap F.op) ≅ sliceOver (SSet.opFunctor.map (nerveMap F)) :=
  kanSliceDiagramIso (kanNerveOppositeIso I) (kanNerveOppositeIso C) _ _
    (kanNerveOppositeIso_natural I F)

/-- 概要：余錐の反転を全単射として束ねる。
方針：反転と図式同型の射影公式を使う。
規約：指定した元の図式と余錐を保持する。
使われ方：B5 の局所余極限の双方向比較。 -/
def kanCoconeReverseConeEquiv {K X : SSet.{u}} (p : K ⟶ X) :
    JoinCocone p ≃ JoinCone (SSet.opFunctor.map p) :=
  (SSet.opObjEquiv (X := sliceUnder p) (n := Opposite.op ⦋0⦌)).symm.trans
    (kanIsoVertexEquiv (kanSliceUnderOpIso p))

/-- 概要：通常の余錐と反対図式の錐の全単射。
方針：反転と図式同型の射影公式を使う。
規約：指定した元の図式と余錐を保持する。
使われ方：B5 の局所余極限の双方向比較。 -/
def kanCoconeOpEquiv : Cocone F ≃ Cone F.op where
  toFun := Cocone.op
  invFun := Cone.unop
  left_inv _ := rfl
  right_inv _ := rfl

/-- 概要：通常の余錐と nerve の任意の native な余錐の全単射。
方針：反転と図式同型の射影公式を使う。
規約：指定した元の図式と余錐を保持する。
使われ方：B5 の局所余極限の双方向比較。 -/
def kanNerveCoconeEquiv : Cocone F ≃ JoinCocone (nerveMap F) :=
  (kanCoconeOpEquiv (F := F)).trans ((kanNerveConeEquiv (F := F.op)).trans
    ((kanIsoVertexEquiv (kanNerveOppositeSliceIso (F := F))).trans
      (kanCoconeReverseConeEquiv (nerveMap F)).symm))

end SerrePositivity.InfinityCategories.F1B
