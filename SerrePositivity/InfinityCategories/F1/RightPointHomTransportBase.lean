module

public import SerrePositivity.InfinityCategories.F1.RightPointHomTransport

/-!
概要：元の right Hom 比較の輸送円柱の底を、同じ標準区間比較と厳密に同定する。
方針：選択済み切断の射影の式を使い、点図式の表示変更だけを消去する。
規約：全 Hom の全時刻・全パラメータを保持する。
使われ方：native な錐の Hom の三角形の第一辺の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 点図式の等式による fiber 表示変更は、元の slice の全図式を変えない。 -/
lemma sliceFiberUncurry_transport {A K X : SSet.{u}} {q q' : K ⟶ X}
    (h : q = q') (z : X _⦋0⦌) (a : A ⟶ vertexFiber (sliceOverProjection q') z) :
    sliceOverUncurry ((a ≫ (eqToIso (congrArg
      (fun t ↦ vertexFiber (sliceOverProjection t) z) h)).inv) ≫
        vertexFiberι (sliceOverProjection q) z) =
      sliceOverUncurry (a ≫ vertexFiberι (sliceOverProjection q') z) := by
  subst q'
  simp only [eqToIso_refl, Iso.refl_inv, Category.comp_id]

/-- 同じ選択済みの right Hom 比較の円柱は、元の標準 Hom の辺を厳密に被覆する。 -/
lemma rightPointHomTransportCylinder_base {E B : SSet.{u}} (r : E ⟶ B) [RightFibration r]
    (c : E _⦋0⦌) (x : B _⦋0⦌) :
    (rightPointHomTransportCylinder r c x).h ≫ r =
      (β_ (pinchedHom x (r.app (Opposite.op ⦋0⦌) c)) (Δ[1] : SSet.{u})).hom ≫
        intervalMappingUncurry (pinchedHomToIntervalMappingSpace x (r.app (Opposite.op ⦋0⦌) c)) := by
  change (pointSliceFamilyHomotopy (rightPointHomTransportSliceFamily r c x)).h ≫ r = _
  rw [pointSliceFamilyHomotopy_postcomp, rightPointHomTransportSliceFamily_base]
  simp only [rightFibrationMappingBaseIso, Iso.trans_inv, Iso.symm_inv]
  have h := pinchedHomToIntervalMappingSpace_uncurry
    (𝟙 (pinchedHom x (r.app (Opposite.op ⦋0⦌) c)))
  rw [Category.id_comp] at h
  rw [h, sliceFiberUncurry_transport (SSet.yonedaEquiv_symm_comp c r)]
  rfl

end SerrePositivity.InfinityCategories
