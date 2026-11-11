module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRestrictionYonedaNaturality

/-! # 制限代表加群への閉射と前合成

概要：像の二対象間の閉射を、元の代表加群から制限代表加群への閉射へ送る。
方針：代表比較の後で像の Yoneda 射を制限し、比較の自然性を使う。
規約：任意の dg 関手に適用。使われ方：商の実辺から roof の入力導来射を作る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 像の閉射を、元の代表加群から制限代表加群への閉射へ送る。 -/
def dgRestrictionRepresentableArrow {x z : ClosedCategory A D}
    (k : F.onClosed.obj x ⟶ F.onClosed.obj z) :=
  representableRestrictionMap A D E F x ≫
    (moduleRestriction A D E F.op).map ((dgYoneda A E).onClosed.map k)

/-- 元の閉射の像では、元の Yoneda 射と終点の比較写像の合成になる。 -/
lemma dgRestrictionRepresentableArrow_map {x z : ClosedCategory A D} (f : x ⟶ z) :
    dgRestrictionRepresentableArrow A D E F (F.onClosed.map f) =
      (dgYoneda A D).onClosed.map f ≫ representableRestrictionMap A D E F z :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableRestrictionMap_naturality A D E F f).symm

/-- 元の閉射による前合成は像での合成と可換。 -/
lemma dgRestrictionRepresentableArrow_precomp {q x z : ClosedCategory A D}
    (s : q ⟶ x) (k : F.onClosed.obj x ⟶ F.onClosed.obj z) :
    (dgYoneda A D).onClosed.map s ≫ dgRestrictionRepresentableArrow A D E F k =
      dgRestrictionRepresentableArrow A D E F (F.onClosed.map s ≫ k) := by
  unfold dgRestrictionRepresentableArrow
  rw [← Category.assoc]
  refine (congrArg (fun a => a ≫ (moduleRestriction A D E F.op).map
    ((dgYoneda A E).onClosed.map k))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableRestrictionMap_naturality A D E F s)).trans ?_
  rw [Category.assoc, ← (moduleRestriction A D E F.op).map_comp,
    ← (dgYoneda A E).onClosed.map_comp]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
