module
public import SerrePositivity.KST.SConstruction.SerreCubeTopCellImage

/-! # 元の零次元の最高生成元の像の閉性
概要：元の次数移送を含め、零次元の最高生成元の任意の実鎖射による像は閉じている。
方針：次元と次数の等号を消去し、同じ実射の微分可換性を評価する。
規約：元の生成元と実射。使われ方：native HA の全二点成分の方程式。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の零次元の最高生成元の実像は、同じ元の次数移送後も閉じている。 -/
lemma serreCubeTopCellImage_cast_zero_d (K : Complex A) (d : ℕ) (hd : d = 0)
    (f : serreCubeComplex A d ⟶ K) (k : ℤ) (hk : -(d : ℤ) = k) :
    K.d k (k + 1) (eqToHom (congrArg K.X hk) (serreCubeTopCellImage A K d f)) = 0 := by
  subst d
  subst k
  have hc := ConcreteCategory.congr_hom (f.comm 0 1) (serreCubeTopCell A 0)
  have h := (congrArg (fun x => f.f 0 x) (serreCubeOrientedTopCell_zero A))
  exact (congrArg (fun x => K.d 0 1 x) h).trans
    (hc.trans ((congrArg (fun x => f.f 1 x) (serreCubeTopCell_zero_d A)).trans (map_zero _)))

end SerrePositivity.KST.SConstruction
