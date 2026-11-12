module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorBoundaryComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftAnodynePushoutProduct

/-!
概要：底の図式と境界写像がパラメーターとともに動く相対 lift 空間。
方針：境界制限の相対内部 Hom をデータの族へ引き戻す。
規約：底と境界の両方を厳密に保持する。
使われ方：区間の分類図式の族上へ境界固定の円柱比較を束ねる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 概要：底と境界の二つの関手族を相対内部 Hom のデータに束ねる。
方針：二つの関手空間の射と可換性を引き戻しへ持ち上げる。
規約：パラメーターの族は任意。
使われ方：動く分類図式の境界固定 lift 空間の底の射。 -/
def relativeBoundaryFamilyData {A C E B L : SSet.{u}} (i : C ⟶ A) (p : E ⟶ B)
    (r : internalHom.PullbackObjObj i p) (v : L ⟶ (ihom C).obj E)
    (a : L ⟶ (ihom A).obj B)
    (h : v ≫ (ihom C).map p = a ≫ (pre i).app B) : L ⟶ r.pt :=
  r.isPullback.lift v a h

/-- 概要：データの境界成分を回収する。
方針：相対内部 Hom の第一射影。
規約：全高次パラメーターでの等式。
使われ方：境界固定の評価の確認。 -/
lemma relativeBoundaryFamilyData_fst {A C E B L : SSet.{u}} (i : C ⟶ A) (p : E ⟶ B)
    (r : internalHom.PullbackObjObj i p) (v : L ⟶ (ihom C).obj E)
    (a : L ⟶ (ihom A).obj B) (h : v ≫ (ihom C).map p = a ≫ (pre i).app B) :
    relativeBoundaryFamilyData i p r v a h ≫ r.fst = v := r.isPullback.lift_fst _ _ _

/-- 概要：データの底の分類図式を回収する。
方針：相対内部 Hom の第二射影。
規約：分類図式もパラメーターとともに動く。
使われ方：同じ底の族を覆う条件。 -/
lemma relativeBoundaryFamilyData_snd {A C E B L : SSet.{u}} (i : C ⟶ A) (p : E ⟶ B)
    (r : internalHom.PullbackObjObj i p) (v : L ⟶ (ihom C).obj E)
    (a : L ⟶ (ihom A).obj B) (h : v ≫ (ihom C).map p = a ≫ (pre i).app B) :
    relativeBoundaryFamilyData i p r v a h ≫ r.snd = a := r.isPullback.lift_snd _ _ _

/-- 概要：動く底と境界を持つ全 lift の空間。
方針：相対内部 Hom の比較射を任意のデータの族へ引き戻す。
規約：指定した lift の存在は仮定しない。
使われ方：分類図式の族全体を覆う比較の定義域。 -/
def relativeBoundaryFamilySpace {A C E B L : SSet.{u}} {i : C ⟶ A} {p : E ⟶ B}
    (r : internalHom.PullbackObjObj i p) (d : L ⟶ r.pt) : SSet.{u} := pullback r.π d

/-- 概要：全境界固定 lift の空間のパラメーター射影。
方針：引き戻しの第二射影。
規約：底と境界の両方を指定するパラメーターへ写す。
使われ方：fiber ごとの比較を族全体へ戻す。 -/
def relativeBoundaryFamilyProjection {A C E B L : SSet.{u}} {i : C ⟶ A} {p : E ⟶ B}
    (r : internalHom.PullbackObjObj i p) (d : L ⟶ r.pt) :
    relativeBoundaryFamilySpace r d ⟶ L := pullback.snd _ _

/-- 概要：境界固定 lift の普遍的な全空間の関手の族。
方針：引き戻しの第一射影。
規約：全高次パラメーターを保持する。
使われ方：普遍評価と円柱への制限。 -/
def relativeBoundaryFamilyCurry {A C E B L : SSet.{u}} {i : C ⟶ A} {p : E ⟶ B}
    (r : internalHom.PullbackObjObj i p) (d : L ⟶ r.pt) :
    relativeBoundaryFamilySpace r d ⟶ (ihom A).obj E := pullback.fst _ _

/-- 概要：境界包含が単射なら族の射影は left fibration。
方針：相対内部 Hom の left fibration 性を底変換する。
規約：パラメーターの充填性は不要。
使われ方：境界固定の族の同値を fiber ごとに判定する。 -/
instance relativeBoundaryFamilyProjection_leftFibration {A C E B L : SSet.{u}}
    (i : C ⟶ A) [Mono i] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (r : internalHom.PullbackObjObj i p) (d : L ⟶ r.pt) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (relativeBoundaryFamilyProjection r d) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration r.π := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_pullbackObjObjπ i p r
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := r.π))⟩

/-- 概要：普遍的な全空間の族は指定した境界の族へ制限される。
方針：引き戻し条件を第一射影で評価する。
規約：境界のパラメーター依存を保持する。
使われ方：普遍 lift の境界条件。 -/
lemma relativeBoundaryFamilyCurry_boundary {A C E B L : SSet.{u}} {i : C ⟶ A} {p : E ⟶ B}
    (r : internalHom.PullbackObjObj i p) (d : L ⟶ r.pt) :
    relativeBoundaryFamilyCurry r d ≫ (pre i).app E =
      relativeBoundaryFamilyProjection r d ≫ d ≫ r.fst := by
  have h := congrArg (fun w ↦ w ≫ r.fst) (pullback.condition (f := r.π) (g := d))
  simp only [Category.assoc, Functor.PullbackObjObj.π_fst, internalHom, Quiver.Hom.unop_op] at h
  exact h

/-- 概要：普遍的な全空間の族は指定した底の図式を覆う。
方針：引き戻し条件を第二射影で評価する。
規約：底の図式のパラメーター依存を保持する。
使われ方：円柱比較の同じ底の族上での可換性。 -/
lemma relativeBoundaryFamilyCurry_base {A C E B L : SSet.{u}} {i : C ⟶ A} {p : E ⟶ B}
    (r : internalHom.PullbackObjObj i p) (d : L ⟶ r.pt) :
    relativeBoundaryFamilyCurry r d ≫ (ihom A).map p =
      relativeBoundaryFamilyProjection r d ≫ d ≫ r.snd := by
  have h := congrArg (fun w ↦ w ≫ r.snd) (pullback.condition (f := r.π) (g := d))
  simp only [Category.assoc, Functor.PullbackObjObj.π_snd, internalHom] at h
  exact h

/-- 概要：quasicategory のパラメーター上の境界固定 lift 空間は quasicategory。
方針：パラメーター射影の left fibration 性を使う。
規約：底の単体集合自体の充填性は不要。
使われ方：族全体の射の同値性の型を与える。 -/
instance relativeBoundaryFamilySpace_quasicategory {A C E B L : SSet.{u}}
    (i : C ⟶ A) [Mono i] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [Quasicategory L]
    (r : internalHom.PullbackObjObj i p) (d : L ⟶ r.pt) :
    Quasicategory (relativeBoundaryFamilySpace r d) :=
  quasicategory_of_innerFibration (relativeBoundaryFamilyProjection r d)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
