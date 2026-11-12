module
public import SerrePositivity.KST.SConstruction.DGGluingAxesComparisons
public import SerrePositivity.KST.SConstruction.DGGluingAxesComplex

/-! # 同じ二軸短複体の元の閉零射に関する関手性
概要：元の三対象・二射・合成零を、同じ閉零射の短複体値関手へ束ねる。
方針：全 Hom 自然性から得た同じ自然比較で二正方形を作り、元の関手法則を保持する。
規約：全次数比較は別宣言のまま保持。使われ方：元の Yoneda 円錐比較の入力自然性。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))

/-- 元の同じ二軸短複体を、元の閉零射に関する実関手へ束ねる。 -/
def dgGluingAxesShortComplexFunctor : ClosedCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) ⥤
    ShortComplex (ClosedCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)) where
  obj X := dgGluingAxesShortComplex R C D M zc hc zd hd (ForgetEnrichment.to (Complex R) X)
  map f :=
    { τ₁ := ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M).comp (dgGluingRightAxis R C D M zc hc)).onClosed.map f
      τ₂ := (DGFunctor.id (A := R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)).onClosed.map f
      τ₃ := ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M).comp (dgGluingLeftAxis R C D M zd hd)).onClosed.map f
      comm₁₂ := (dgGluingAxisRightClosedComparison R C D M zc hc).naturality f
      comm₂₃ := (dgGluingAxisLeftClosedComparison R C D M zd hd).naturality f }
  map_id X := by
    apply ShortComplex.hom_ext
    · exact ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M).comp (dgGluingRightAxis R C D M zc hc)).onClosed.map_id X
    · exact (DGFunctor.id (A := R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)).onClosed.map_id X
    · exact ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M).comp (dgGluingLeftAxis R C D M zd hd)).onClosed.map_id X
  map_comp f g := by
    apply ShortComplex.hom_ext
    · exact ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M).comp
        (dgGluingRightAxis R C D M zc hc)).onClosed.map_comp f g
    · exact (DGFunctor.id (A := R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)).onClosed.map_comp f g
    · exact ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M).comp
        (dgGluingLeftAxis R C D M zd hd)).onClosed.map_comp f g

/-- 同じ短複体値関手は、元の対象を中央対象として厳密に保持する。 -/
lemma dgGluingAxesShortComplexFunctor_middle (X : ClosedCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)) :
    ((dgGluingAxesShortComplexFunctor R C D M zc hc zd hd).obj X).X₂ = X := rfl

/-- 同じ短複体値関手の中央成分は、元の同じ閉零射そのもの。 -/
lemma dgGluingAxesShortComplexFunctor_middle_map
    {X Y : ClosedCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)} (f : X ⟶ Y) :
    ((dgGluingAxesShortComplexFunctor R C D M zc hc zd hd).map f).τ₂ = f :=
  (congrArg (ForgetEnrichment.homOf (Complex R))
    (Category.comp_id (ForgetEnrichment.homTo (Complex R) f))).trans
      (ForgetEnrichment.homOf_homTo (Complex R) f)

end SerrePositivity.KST.SConstruction
