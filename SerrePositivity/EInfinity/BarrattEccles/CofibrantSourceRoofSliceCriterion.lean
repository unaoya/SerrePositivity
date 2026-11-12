module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofSliceFibration
public import SerrePositivity.EInfinity.FrameHom.FrameRoofSliceWeakContractibility

/-!
# 元の積単体からの全錐比較による屋根 cofinality の還元

概要：元の sourceFrameHom×Δ[n] の全単体から実相対 corner への一つの射を指定する。
方針：既存の次数同型を戻し、Kan 引き戻し不変性と Quillen A を接続する。
規約：この射の弱同値性は未証明であり、普遍性の結論を入力とはしない。
使われ方：元の Kan Hom 高次比較との照合後の実 slice の弱可縮性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits Opposite SSet
open SerrePositivity.EInfinity.FrameHom.FrameArrows SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

def cofibrantSourceRoofProductCornerMap : nerve (cofibrantSourceRoofProductElements A X Y b) ⟶
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCorner (SSet.yonedaEquiv.symm b) (cofibrantSourceRoofProjection A X Y) :=
  (cofibrantSourceRoofProductIso A X Y b).hom ≫
    (cofibrantSourceRoofDegreeTransportIso A X Y b).inv ≫
      roofQuillenDegreeCornerMap (cofibrantDKSourceFrame A X)
        (show (cofibrantAlgebraRelativeCategory A).category from Y)
        (SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
        b (cofibrantSourceFrameRoofMap A X Y)

lemma cofibrantSourceRoofSlice_weaklyContractible_of_productCorner_weak
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (cofibrantSourceRoofProductCornerMap A X Y b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (cofibrantSourceRoofSlice A X Y b) := by
  have := cofibrantSourceRoofProjection_leftFibration A X Y
  let e := cofibrantSourceRoofProductIso A X Y b ≪≫
    (cofibrantSourceRoofDegreeTransportIso A X Y b).symm
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso e).isWeakHomotopyEquivalence
  apply roofQuillenSlice_weaklyContractible_of_corner_weak (cofibrantDKSourceFrame A X)
    (show (cofibrantAlgebraRelativeCategory A).category from Y)
    (SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
    b (cofibrantSourceFrameRoofMap A X Y)
  exact he.cancel_left h

lemma cofibrantSourceRoofMap_isLeftCofinal_of_productCorner_weak
    (h : ∀ b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (cofibrantSourceRoofProductCornerMap A X Y b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (cofibrantSourceFrameRoofMap A X Y) :=
  (cofibrantSourceRoofMap_isLeftCofinal_iff_slices A X Y).2
    (fun b => cofibrantSourceRoofSlice_weaklyContractible_of_productCorner_weak A X Y b (h b))

end SerrePositivity.EInfinity.BarrattEccles
