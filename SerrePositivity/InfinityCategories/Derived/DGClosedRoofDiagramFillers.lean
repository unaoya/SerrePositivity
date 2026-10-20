module
public import SerrePositivity.InfinityCategories.Derived.DGClosedRoofDiagramComparison
public import SerrePositivity.InfinityCategories.Derived.DGQuotientRoofLocallyConstant
public import SerrePositivity.InfinityCategories.Derived.RoofRelativeTransportHomotopy
public import SerrePositivity.InfinityCategories.Derived.RoofHomotopyRelativeFiller

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve SSet MonoidalCategory
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
variable (P : Set D) (x y : D) {s' s : DGClosedVerdierDenominators A D P x} (R : s' ⟶ s)
variable {L K : SSet.{max u v}} (i : L ⟶ K) [Mono i]
variable (b : L ⟶ DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) y)
variable (g : K ⟶ DGNerve.pinchedHom A (QuotientObject D P)
  ((inclusion A D P).obj (ForgetEnrichment.to (Complex A) s.obj.left))
  ((inclusion A D P).obj y))
variable (t : K ⟶ DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) s'.obj.left) y)

/-- 一般相対係数充填は、同じ指定部分を持つ実屋根の相対充填を与える。 -/
theorem dgClosedRoofDiagramFiller_nonempty (hP : localKFlat A D P)
    (hb : b ≫ pinchedHomChainMap ((inclusion A D P).map
      (ForgetEnrichment.to (Complex A) s.obj.left) y) = i ≫ g)
    (ht : i ≫ t = b ≫ pinchedClosedPrecomposition A D (y := y) R.hom.left)
    (C : SSet.Homotopy
      (g ≫ pinchedClosedPrecomposition A (QuotientObject D P)
        (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map R.hom.left))
      (t ≫ pinchedHomChainMap ((inclusion A D P).map
        (ForgetEnrichment.to (Complex A) s'.obj.left) y)))
    (hC : (i ▷ (Δ[1] : SSet.{max u v})) ≫ C.h =
      CartesianMonoidalCategory.fst L Δ[1] ≫ i ≫ g ≫
        pinchedClosedPrecomposition A (QuotientObject D P)
          (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map R.hom.left)) :
    Nonempty (RoofHomotopyRelativeFiller i (dgRoofCorrespondenceMap A D P x y)
      (b ≫ dgClosedRoofHomInclusion A D P x y s)
      (g ≫ dgQuotientClosedRoofHomInclusion A D P x y s)) := by
  have := dgQuotientRoofCorrespondenceProjection_leftFibration A D P hP x y
  let Cp := dgClosedRoofDiagramComparison A D P x y R g t C
  let Tp := dgQuotientRoofDiagramTransport A D P x y R g
  have hCp := roofHomotopy_over_constant Cp (dgQuotientRoofCorrespondenceProjection A D P x y)
    (dgClosedVerdierDenominatorVertex A D P x s')
    (dgClosedRoofDiagramComparison_projection A D P x y R g t C)
  obtain ⟨T⟩ := roofRelativeTransportTriangle_nonempty
    (dgQuotientRoofCorrespondenceProjection A D P x y) i Cp Tp
    (dgClosedRoofDiagramComparison_fixed A D P x y R i g t C hC) hCp
  let u := t ≫ dgClosedRoofHomInclusion A D P x y s'
  let B := dgClosedRoofDiagramBoundaryTransport A D P x y R i b t ht
  let H := stableHomotopyRetarget T.homotopy (Category.assoc _ _ _).symm rfl
  refine ⟨⟨u, B, H, ?_⟩⟩
  have hh : H.h = T.homotopy.h := homotopyRetarget_h _ _ _
  rw [hh]
  exact T.homotopy_boundary.trans
    (dgClosedRoofDiagramTransport_boundary A D P x y R i b g t ht hb)

end SerrePositivity.InfinityCategories
