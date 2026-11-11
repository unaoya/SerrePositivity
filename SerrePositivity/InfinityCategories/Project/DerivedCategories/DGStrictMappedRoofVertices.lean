module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictMappedRoofNerveMap

/-! # 写した閉分子を持つ厳密屋根の実頂点

概要：元の閉実分母と任意の像の閉分子から実屋根の頂点を作り、両射影を照合する。
方針：厳密屋根 nerve の指定零単体を写し、閉分母・閉分子の頂点公式へ戻す。
規約：像の閉分子は元から持ち上がると仮定しない。使われ方：商の任意の分子の細分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]
variable (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)

/-- 指定元の閉実分母と、像の任意の閉分子を持つ実屋根の頂点。 -/
def dgStrictMappedRoofVertex (P : Set D) (x : D) (y : E)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)
    (f : F.onClosed.obj s.obj.left ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgMappedRoofCorrespondence A D E F P x y) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofNerveMap A D E F P x y).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofMk A D E F P x y s f))

/-- 写した閉分子の実屋根頂点は、元の指定閉分母を厳密に回収する。 -/
lemma dgStrictMappedRoofVertex_projection (P : Set D) (x : D) (y : E)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)
    (f : F.onClosed.obj s.obj.left ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) :
    (pullback.snd _ _ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgMappedRoofCorrespondence A D E F P x y ⟶ _).app
      (Opposite.op ⦋0⦌) (dgStrictMappedRoofVertex A D E F P x y s f) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x s := by
  have h := congrArg (fun G => G.app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofMk A D E F P x y s f)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofNerveMap_projection A D E F P x y)
  refine h.trans ?_
  exact (congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofVerdierMap A D P x).app (Opposite.op ⦋0⦌) z)
    (nerveMap_app_mk₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofDenominator A D E F P x y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofMk A D E F P x y s f))).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofVerdierMap_vertex A D P x s)

/-- 写した閉分子の実屋根頂点は、指定した像の閉分子の slice 頂点を回収する。 -/
lemma dgStrictMappedRoofVertex_target (P : Set D) (x : D) (y : E)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)
    (f : F.onClosed.obj s.obj.left ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgMappedRoofCorrespondenceTarget A D E F P x y).app (Opposite.op ⦋0⦌)
      (dgStrictMappedRoofVertex A D E F P x y s f) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex A E f := by
  have h := congrArg (fun G => G.app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofMk A D E F P x y s f)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofNerveMap_target A D E F P x y)
  refine h.trans ?_
  exact (congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedNerveOverMap A E y).app (Opposite.op ⦋0⦌) z)
    (nerveMap_app_mk₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofNumerator A D E F P x y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofMk A D E F P x y s f))).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedNerveOverMap_vertex A E y (Over.mk f))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
