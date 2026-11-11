module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictMappedRoofEdges

/-! # 指定された商分子と元の閉細分の実屋根辺

概要：元の閉実分母と任意の閉商分子を持つ実商屋根の頂点・細分辺を公開する。
方針：一般の mapped 屋根を Drinfeld 包含へ特殊化する。
規約：商分子の持ち上げを仮定しない。使われ方：有限相対充填の実商屋根への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 実商屋根から、その指定終点の分子の slice への射影。 -/
def dgQuotientRoofCorrespondenceTarget (P : Set D) (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondence A D P x y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)).symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj y))) :=
  pullback.fst _ _

/-- 元の指定閉分母と、持ち上げを仮定しない指定閉商分子の実商屋根頂点。 -/
def dgStrictQuotientRoofVertex (P : Set D) (x y : D)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)
    (f : (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.obj s.obj.left ⟶
      ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondence A D P x y) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofVertex A D (DGQuotient.QuotientObject D P)
    (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P) P x ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) s f

/-- 指定商屋根頂点の分母は元の指定閉分母。 -/
lemma dgStrictQuotientRoofVertex_projection (P : Set D) (x y : D)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)
    (f : (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.obj s.obj.left ⟶
      ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y).app (Opposite.op ⦋0⦌)
      (dgStrictQuotientRoofVertex A D P x y s f) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x s :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofVertex_projection A D (DGQuotient.QuotientObject D P)
    (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P) P x ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) s f

/-- 指定商屋根頂点の分子は任意に指定した閉商分子そのもの。 -/
lemma dgStrictQuotientRoofVertex_target (P : Set D) (x y : D)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)
    (f : (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.obj s.obj.left ⟶
      ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)) :
    (dgQuotientRoofCorrespondenceTarget A D P x y).app (Opposite.op ⦋0⦌)
      (dgStrictQuotientRoofVertex A D P x y s f) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex A (DGQuotient.QuotientObject D P) f :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofVertex_target A D (DGQuotient.QuotientObject D P)
    (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P) P x ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) s f

/-- 指定元の細分射と任意の閉商分子を持つ、実商屋根の指定辺。 -/
def dgStrictQuotientRoofRefinementEdge (P : Set D) (x y : D)
    {s t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (r : s ⟶ t)
    (f : (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.obj t.obj.left ⟶
      ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondence A D P x y).Edge
      (dgStrictQuotientRoofVertex A D P x y s
        ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map r.hom.left ≫ f))
      (dgStrictQuotientRoofVertex A D P x y t f) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofRefinementEdge A D (DGQuotient.QuotientObject D P)
    (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P) P x ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) r f

/-- 指定実商細分辺は、元の実分母辺を厳密に保つ。 -/
lemma dgStrictQuotientRoofRefinementEdge_projection (P : Set D) (x y : D)
    {s t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (r : s ⟶ t)
    (f : (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.obj t.obj.left ⟶
      ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y).app (Opposite.op ⦋1⦌)
      (dgStrictQuotientRoofRefinementEdge A D P x y r f).edge =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofVerdierMap A D P x).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ r) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofRefinementEdge_projection A D (DGQuotient.QuotientObject D P)
    (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P) P x ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) r f

/-- 指定実商細分辺の分子は、包含像による厳密前合成三角形。 -/
lemma dgStrictQuotientRoofRefinementEdge_target (P : Set D) (x y : D)
    {s t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (r : s ⟶ t)
    (f : (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.obj t.obj.left ⟶
      ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)) :
    (dgQuotientRoofCorrespondenceTarget A D P x y).app (Opposite.op ⦋1⦌)
      (dgStrictQuotientRoofRefinementEdge A D P x y r f).edge =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedNerveOverMap A (DGQuotient.QuotientObject D P)
        ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁
          (Over.homMk ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map r.hom.left) rfl :
            Over.mk ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map r.hom.left ≫ f) ⟶
              Over.mk f)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofRefinementEdge_target A D (DGQuotient.QuotientObject D P)
    (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P) P x ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) r f

end SerrePositivity.InfinityCategories.Project.DerivedCategories
