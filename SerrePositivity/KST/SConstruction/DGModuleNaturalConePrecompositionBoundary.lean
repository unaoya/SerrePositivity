module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConePrecomposition

/-!
概要：元前合成 cone 全比較が指定右包含を全厳密に保持することを示す。
方針：同じ実 cone 射の包含等式を全閉成分へ回収する。
規約：成分だけでなく全厳密比較の等号を保持する。
使われ方：元実逆回転比較の指定上二単体。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type w} [DGCategory R P]
  (F G H : DGFunctor R P (RightModule R D))
  (α : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (β : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans G H)
local notation "γ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp α β
local notation "CB" => dgModuleNaturalConeFunctor R D G H β
local notation "CC" => dgModuleNaturalConeFunctor R D F H (γ)

/-- 概要：元前合成 cone 全比較の右包含制限は元右包含そのもの。
方針：閉成分の外延性と同じ実 cone map の包含回収を使う。
規約：全厳密比較の等号。使われ方：元実逆回転の指定境界。 -/
lemma dgModuleNaturalConePrecomposition_inr :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (dgModuleNaturalConeInr R D F H (γ))
      (dgModuleNaturalConePrecomposition R D F G H α β) =
        dgModuleNaturalConeInr R D G H β := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_ext
  intro x
  apply (closedHomEquiv R (RightModule R D) (H.obj x) ((CB).obj x)).symm.injective
  change dgModuleNaturalConeArrow R D H (CB)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (dgModuleNaturalConeInr R D F H (γ))
      (dgModuleNaturalConePrecomposition R D F G H α β)) x =
    dgModuleNaturalConeArrow R D H (CB) (dgModuleNaturalConeInr R D G H β) x
  rw [dgModuleNaturalConeArrow_comp, dgModuleNaturalConeInr_arrow,
    dgModuleNaturalConePrecomposition_arrow]
  exact (moduleConeMapOfHomotopy_inr R D
    (dgModuleNaturalConeArrow R D F H (γ) x) (dgModuleNaturalConeArrow R D G H β x)
    (dgModuleNaturalConeArrow R D F G α x) (𝟙 _)
    (dgModuleNaturalConePrecompositionSquareHomotopy R D F G H α β x)).trans
      ((Category.id_comp _).trans (dgModuleNaturalConeInr_arrow R D G H β x).symm)
end SerrePositivity.KST.SConstruction
