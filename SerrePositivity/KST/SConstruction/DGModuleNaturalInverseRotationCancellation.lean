module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalInverseRotation
public import SerrePositivity.KST.SConstruction.DGModuleShiftCancellationNative

/-!
概要：元全逆回転の相殺因子の閉射を同じ指定相殺へ回収する。
方針：入力関手の同じ斉次作用への制限の成分を照合する。
規約：元指定閉射を保持する。
使われ方：元実逆回転全比較の第三因子の同値認証。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
variable {P : Type (max (u + 1) v)} [DGCategory R P]
  (G : DGFunctor R P (RightModule R D))

/-- 概要：同じ全逆回転の相殺因子は元指定相殺の同じ閉射を回収する。
方針：同じ入力制限の閉射成分を照合する。
規約：指定相殺成分を変更しない。使われ方：第三因子の実同値判定。 -/
lemma dgModuleNaturalInverseRotationCancellation_arrow (x : P) :
    dgModuleNaturalConeArrow R D ((G.comp (moduleShiftDG R D 1)).comp (moduleShiftDG R D (-1)))
      G (dgModuleNaturalInverseRotationCancellation R D G) x =
      dgModuleNaturalConeArrow R D
        ((moduleShiftDG R D 1).comp (moduleShiftDG R D (-1)))
        (DGFunctor.id (RightModule R D)) (dgModuleSpecifiedCancellationStrictComparison R D)
        (G.obj x) := rfl
end SerrePositivity.KST.SConstruction
