module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.PointHomTransportCylinder

/-!
概要：全 Hom の輸送円柱の底を、元の左 Hom の標準区間比較と厳密に同定する。
方針：coslice の族の底を標準 fiber 表示へ戻し、円柱の自然性を使う。
規約：全単体・全時刻での等式。
使われ方：余錐の正方形の右辺が元の全 Hom の辺であることの検証。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (d : E _⦋0⦌) (y : B _⦋0⦌)

/-- 概要：fiber の点図式の等式による表示変更は元の join 図式を変えない。
方針：等式を消去する。規約：両図式の形は同じ。使われ方：底の標準化の消去。 -/
lemma cosliceFiberUncurry_transport {A K X : SSet.{u}} {q q' : K ⟶ X}
    (h : q = q') (z : X _⦋0⦌) (a : A ⟶ vertexFiber (sliceUnderProjection q') z) :
    sliceUnderUncurry ((a ≫ (eqToIso (congrArg
      (fun t ↦ vertexFiber (sliceUnderProjection t) z) h)).inv) ≫
        vertexFiberι (sliceUnderProjection q) z) =
      sliceUnderUncurry (a ≫ vertexFiberι (sliceUnderProjection q') z) := by
  subst q'
  simp only [eqToIso_refl, Iso.refl_inv, Category.comp_id]

/-- 概要：指定始点の全 Hom の輸送円柱は元の標準左 Hom 区間比較を被覆する。
方針：coslice の射影と fiber の表示変更を消去し、区間比較の uncurry を用いる。
規約：元の底の全 Hom を保持。使われ方：全族の合成三角形の右辺。 -/
lemma pointHomTransportCylinder_base :
    (pointHomTransportCylinder p d y).h ≫ p =
      (β_ (pinchedHomLeft (p.app (Opposite.op ⦋0⦌) d) y) (Δ[1] : SSet.{u})).hom ≫
        intervalMappingUncurry (pinchedHomLeftToIntervalMappingSpace
          (p.app (Opposite.op ⦋0⦌) d) y) := by
  change (pointCosliceFamilyHomotopy (pointHomTransportCosliceFamily p d y)).h ≫ p = _
  rw [pointCosliceFamilyHomotopy_postcomp, pointHomTransportCosliceFamily_base]
  simp only [leftFibrationInitialBaseIso, Iso.trans_inv]
  rw [pinchedHomLeftToIntervalMappingSpace, cosliceFiberToIntervalMappingSpace_uncurry]
  rw [cosliceFiberUncurry_transport (SSet.yonedaEquiv_symm_comp d p)]
  rfl

end SerrePositivity.InfinityCategories.F2
