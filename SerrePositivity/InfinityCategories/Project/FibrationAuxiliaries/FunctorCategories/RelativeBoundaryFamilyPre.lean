module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeHomBoundaryFiber

/-!
概要：動く底と境界を持つ全 lift 空間の前合成による比較。
方針：相対内部 Hom のデータと全空間を同時に前合成する。
規約：パラメーター射影を厳密に保つ。
使われ方：分類図式の族全体における輸送円柱比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 概要：定義域の前合成は底と境界の相対データの射を誘導する。
方針：境界成分を保ち底の図式を前合成する。
規約：全ての射と単体集合は任意。
使われ方：境界固定の族の同じパラメーター上の比較。 -/
def relativeBoundaryDataPre {A D C E B : SSet.{u}} (i : D ⟶ A) (j : C ⟶ D) (p : E ⟶ B)
    (rA : internalHom.PullbackObjObj (j ≫ i) p) (rD : internalHom.PullbackObjObj j p) :
    rA.pt ⟶ rD.pt :=
  rD.isPullback.lift rA.fst (rA.snd ≫ (pre i).app B) (by
    have h := rA.isPullback.w
    change rA.fst ≫ (ihom C).map p = rA.snd ≫ (pre (j ≫ i)).app B at h
    change rA.fst ≫ (ihom C).map p = (rA.snd ≫ (pre i).app B) ≫ (pre j).app B
    rw [Category.assoc, ← NatTrans.comp_app, ← pre_map]
    exact h)

/-- 概要：データの前合成は境界成分を保つ。
方針：引き戻しの第一射影。
規約：境界の族全体の等式。
使われ方：同じ境界を固定した比較。 -/
lemma relativeBoundaryDataPre_fst {A D C E B : SSet.{u}}
    (i : D ⟶ A) (j : C ⟶ D) (p : E ⟶ B)
    (rA : internalHom.PullbackObjObj (j ≫ i) p) (rD : internalHom.PullbackObjObj j p) :
    relativeBoundaryDataPre i j p rA rD ≫ rD.fst = rA.fst := rD.isPullback.lift_fst _ _ _

/-- 概要：データの前合成の底成分は元の底の図式の前合成。
方針：引き戻しの第二射影。
規約：底のパラメーター依存を保持する。
使われ方：同じ分類図式の族を覆うことの確認。 -/
lemma relativeBoundaryDataPre_snd {A D C E B : SSet.{u}}
    (i : D ⟶ A) (j : C ⟶ D) (p : E ⟶ B)
    (rA : internalHom.PullbackObjObj (j ≫ i) p) (rD : internalHom.PullbackObjObj j p) :
    relativeBoundaryDataPre i j p rA rD ≫ rD.snd = rA.snd ≫ (pre i).app B :=
  rD.isPullback.lift_snd _ _ _

/-- 概要：全空間の前合成と相対データの前合成は厳密に可換。
方針：相対内部 Hom の二射影で比較する。
規約：底と境界を同時に保持する。
使われ方：族の引き戻し空間への比較の可換条件。 -/
lemma relativeBoundaryDataPre_π {A D C E B : SSet.{u}}
    (i : D ⟶ A) (j : C ⟶ D) (p : E ⟶ B)
    (rA : internalHom.PullbackObjObj (j ≫ i) p) (rD : internalHom.PullbackObjObj j p) :
    (pre i).app E ≫ rD.π = rA.π ≫ relativeBoundaryDataPre i j p rA rD := by
  apply rD.hom_ext
  · rw [Category.assoc, rD.π_fst, Category.assoc, relativeBoundaryDataPre_fst, rA.π_fst]
    simp only [internalHom, Quiver.Hom.unop_op]
    rw [pre_map, NatTrans.comp_app]
  · rw [Category.assoc, rD.π_snd, Category.assoc, relativeBoundaryDataPre_snd,
      ← Category.assoc rA.π, rA.π_snd]
    exact (pre i).naturality p |>.symm

/-- 概要：前合成により動く底と境界の全 lift 空間を比較する。
方針：全空間の射を前合成しパラメーターはそのまま引き戻しへ持ち上げる。
規約：比較射 i の単射性は要求しない。
使われ方：分類図式の族全体を覆う輸送円柱比較。 -/
def relativeBoundaryFamilyPre {A D C E B L : SSet.{u}}
    (i : D ⟶ A) (j : C ⟶ D) (p : E ⟶ B)
    (rA : internalHom.PullbackObjObj (j ≫ i) p) (rD : internalHom.PullbackObjObj j p)
    (d : L ⟶ rA.pt) : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilySpace rA d ⟶
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilySpace rD (d ≫ relativeBoundaryDataPre i j p rA rD) :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyCurry rA d ≫ (pre i).app E)
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyProjection rA d) (by
      rw [Category.assoc, relativeBoundaryDataPre_π, ← Category.assoc]
      change (pullback.fst _ _ ≫ rA.π) ≫ _ = _
      rw [pullback.condition, Category.assoc]
      rfl)

/-- 概要：族の前合成は全空間の関手空間への射を前合成する。
方針：引き戻しの第一射影。
規約：全高次パラメーターでの式。
使われ方：fiber 上の比較を固定図式の比較へ同定する。 -/
lemma relativeBoundaryFamilyPre_curry {A D C E B L : SSet.{u}}
    (i : D ⟶ A) (j : C ⟶ D) (p : E ⟶ B)
    (rA : internalHom.PullbackObjObj (j ≫ i) p) (rD : internalHom.PullbackObjObj j p)
    (d : L ⟶ rA.pt) : relativeBoundaryFamilyPre i j p rA rD d ≫
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyCurry rD (d ≫ relativeBoundaryDataPre i j p rA rD) =
        _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyCurry rA d ≫ (pre i).app E := pullback.lift_fst _ _ _

/-- 概要：族の前合成はパラメーター射影を厳密に保つ。
方針：引き戻しの第二射影。
規約：底のパラメーター空間の射は恒等。
使われ方：族の fiber ごとの同値判定。 -/
lemma relativeBoundaryFamilyPre_projection {A D C E B L : SSet.{u}}
    (i : D ⟶ A) (j : C ⟶ D) (p : E ⟶ B)
    (rA : internalHom.PullbackObjObj (j ≫ i) p) (rD : internalHom.PullbackObjObj j p)
    (d : L ⟶ rA.pt) : relativeBoundaryFamilyPre i j p rA rD d ≫
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyProjection rD (d ≫ relativeBoundaryDataPre i j p rA rD) =
        _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyProjection rA d := pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
