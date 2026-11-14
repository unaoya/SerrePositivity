module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGClosedRoofDiagramComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientRoofLocallyConstant
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofRelativeTransportHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofHomotopyRelativeFiller

/-! # 一般係数充填の実屋根への接続

概要：一般対の境界固定係数充填から、元の閉実分母上の屋根問題の相対充填を構成する。
方針：係数比較と全体の細分輸送を相対三角形へ充填し、同じ境界輸送と結ぶ。
規約：指定部分の全時刻で元・商輸送を厳密に整合させる。使われ方：有限対の実屋根検査。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet MonoidalCategory
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable (P : Set D) (x y : D) {s' s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (R : s' ⟶ s)
variable {L K : SSet.{max u v}} (i : L ⟶ K) [Mono i]
variable (b : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) y)
variable (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P)
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left))
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y))
variable (t : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (ForgetEnrichment.to (Complex A) s'.obj.left) y)

/-- 一般相対係数充填は、同じ指定部分を持つ実屋根の相対充填を与える。 -/
theorem dgClosedRoofDiagramFiller_nonempty (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (hb : b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left) y) = i ≫ g)
    (ht : i ≫ t = b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D (y := y) R.hom.left)
    (C : SSet.Homotopy
      (g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
        (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map R.hom.left))
      (t ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s'.obj.left) y)))
    (hC : (i ▷ (Δ[1] : SSet.{max u v})) ≫ C.h =
      CartesianMonoidalCategory.fst L Δ[1] ≫ i ≫ g ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
          (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map R.hom.left)) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofHomotopyRelativeFiller i (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y)
      (b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y s)
      (g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofHomInclusion A D P x y s)) := by
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection_leftFibration A D P hP x y
  let Cp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofDiagramComparison A D P x y R g t C
  let Tp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofDiagramTransport A D P x y R g
  have hCp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofHomotopy_over_constant Cp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x s')
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofDiagramComparison_projection A D P x y R g t C)
  obtain ⟨T⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofRelativeTransportTriangle_nonempty
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y) i Cp Tp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofDiagramComparison_fixed A D P x y R i g t C hC) hCp
  let u := t ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y s'
  let B := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofDiagramBoundaryTransport A D P x y R i b t ht
  let H := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget T.homotopy (Category.assoc _ _ _).symm rfl
  refine ⟨⟨u, B, H, ?_⟩⟩
  have hh : H.h = T.homotopy.h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.homotopyRetarget_h _ _ _
  rw [hh]
  exact T.homotopy_boundary.trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofDiagramTransport_boundary A D P x y R i b g t ht hb)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
