module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCellResolvedGraphProjective
public import SerrePositivity.KST.SConstruction.DGGluingCellRightAxisPerfectArrow

/-!
概要：K-S• の同じ右軸・恒等 graph 解像度の射影性を無条件に束ねる。
方針：任意自己関手の一般結果を結論の二フィールドへ適用する。
規約：KST は結論の型のためだけに読み取り専用 import。
使われ方：DGOdotGluing を含む元の全 gluing の利用側。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (z : C) (hz : Limits.IsZero (ForgetEnrichment.of (Complex R) z))

theorem dgGluingCellRightAxisProjectiveInput :
    KST.SConstruction.DGGluingCellRightAxisProjectiveInput R C D M z hz where
  right := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolvedGraph_projective R _ _
  identity := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolvedGraph_projective R _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
