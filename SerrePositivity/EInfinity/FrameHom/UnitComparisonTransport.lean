module
public import SerrePositivity.EInfinity.FrameHom.UnitComparisonWeakDetection
public import SerrePositivity.InfinityCategories.HomotopyLimits.PinchedActionEquivalences
public import SerrePositivity.EInfinity.ComplexLimits.PinchedTransportFamily
/-!
概要：同じ単位と弱な全 pinched 族による判定を、指定した同型で両端輸送する。
方針：元の全族三角形を同じ定値射と区間作用の公式で輸送する。
規約：単位比較自身・実関手・全パラメータを保持する。
使われ方：元の局所化源単位から既存の標準単位比較への弱同値性の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory SSet SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.HomotopyLimits
open scoped Simplicial

/-- 概要：同じ全族三角形と指定端点同型から標準単位誘導射自身は弱同値。
方針：元の二つの弱な族を同じ同型で前後合成し、全族判定に代入する。
規約：点ごとのみへ弱めない。使われ方：標準導来単位の写像空間判定。 -/
lemma unitComparisonTransport_weak {K C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    (U : C ⟶ D) {a b c d : C.obj (Opposite.op ⦋0⦌)}
    {z x : D.obj (Opposite.op ⦋0⦌)} (e : VertexIso a b) (t : VertexIso c d)
    (s : VertexIso z x)
    (η : (HomotopyCategory.mk x : hoFunctor.obj D) ⟶
      HomotopyCategory.mk (U.app (Opposite.op ⦋0⦌) a))
    (ν : (HomotopyCategory.mk z : hoFunctor.obj D) ⟶
      HomotopyCategory.mk (U.app (Opposite.op ⦋0⦌) b))
    (p : K ⟶ pinchedHom b c) (r : K ⟶ pinchedHom z (U.app (Opposite.op ⦋0⦌) c))
    (hp : IsWeakHomotopyEquivalence p) (hr : IsWeakHomotopyEquivalence r)
    (hu : s.hom ≫ η ≫ (hoFunctor.map U).toFunctor.map e.hom = ν)
    (hf : constantFunctorHomMap K ν ≫ intervalFamilyHom
      (p ≫ pinchedHomMap U b c ≫ pinchedHomToIntervalMappingSpace _ _) =
        intervalFamilyHom (r ≫ pinchedHomToIntervalMappingSpace _ _)) :
    IsWeakHomotopyEquivalence (intervalFunctorMap U a d ≫
      intervalPrecompose (U.app (Opposite.op ⦋0⦌) d) η) := by
  let P := (p ≫ PinchedInterval.precompose c e.hom) ≫ PinchedInterval.postcompose a t.hom
  let R := (r ≫ PinchedInterval.precompose (U.app (Opposite.op ⦋0⦌) c) s.inv) ≫
    PinchedInterval.postcompose x ((hoFunctor.map U).toFunctor.map t.hom)
  have hP : IsWeakHomotopyEquivalence P :=
    (hp.comp (pinchedPrecompose_isQCatEquivalence_of_isIso e.hom c).isWeakHomotopyEquivalence).comp
        (pinchedPostcompose_isQCatEquivalence_of_isIso t.hom a).isWeakHomotopyEquivalence
  have hR : IsWeakHomotopyEquivalence R :=
    (hr.comp (pinchedPrecompose_isQCatEquivalence_of_isIso s.inv _).isWeakHomotopyEquivalence).comp
        (pinchedPostcompose_isQCatEquivalence_of_isIso
          ((hoFunctor.map U).toFunctor.map t.hom) x).isWeakHomotopyEquivalence
  have hi := (pinchedHomToIntervalMappingSpace_isQCatEquivalence a d).isWeakHomotopyEquivalence
  refine unitComparison_weak_of_probe_family _ (P ≫ pinchedHomToIntervalMappingSpace a d) R
    (hP.comp hi) hR ?_
  have hu' : η ≫ (hoFunctor.map U).toFunctor.map e.hom = s.inv ≫ ν := by
    rw [← hu]
    simp only [Iso.inv_hom_id_assoc]
  have ht := pinchedTransport_intervalFamily (a := x) (b := z)
    (c := U.app (Opposite.op ⦋0⦌) c) (d := U.app (Opposite.op ⦋0⦌) d) s.inv
    ((hoFunctor.map U).toFunctor.map t.hom) r
  simp only [Category.assoc] at ht
  dsimp only [P, R]
  rw [Category.assoc, ← Category.assoc (pinchedHomToIntervalMappingSpace a d)
    (intervalFunctorMap U a d), ← pinchedHomToIntervalMappingSpace_naturality,
    ← Category.assoc, intervalPrecompose_family, pinchedTransport_forget_family]
  simp only [Category.assoc]
  rw [ht]
  rw [← Category.assoc (constantFunctorHomMap K η)
    (constantFunctorHomMap K ((hoFunctor.map U).toFunctor.map e.hom)),
    ← constantFunctorHomMap_comp, hu', constantFunctorHomMap_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (constantFunctorHomMap K ν), hf]

end SerrePositivity.EInfinity.FrameHom
