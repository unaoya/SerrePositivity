module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.CellAttachments.DGCellSourceProjective
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensor
public import SerrePositivity.KST.SConstruction.DGCellResolvedGraphPerfect

/-!
概要：任意の元 dg 自己関手について同じ固定 graph 解像度の右射影性を供給する。
方針：cell source の全 Hom の K-projective 性を同じ標準 bimodule 解像度へ適用する。
規約：SConstruction の葉は結論の型と固定解像度のためだけに読み取り専用 import。
使われ方：K-S• の右軸・恒等の両条件。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (B : Type v) [DGCategory R B] [Small.{u} B]

lemma dgCellResolvedGraph_projective (F : DGFunctor R B B) :
    KST.SConstruction.DGCellResolvedGraphProjectiveCondition R B F := by
  intro x
  exact (KST.SConstruction.dgCellResolvedGraphResolution R B F).right_homotopicallyProjective R
    (DGCategoryCellResolution.Source R B) (DGCategoryCellResolution.Source R B)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellSourceHom_isKProjective R B) x

end SerrePositivity.InfinityCategories.Project.DerivedCategories
