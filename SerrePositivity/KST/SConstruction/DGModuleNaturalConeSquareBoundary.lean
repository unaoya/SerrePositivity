module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeSquare

/-!
概要：元全 cone square 比較の右包含境界を全厳密に保持する。
方針：同じ元 descent の包含回収を全閉成分の外延性へ適用する。
規約：指定四辺と全厳密等号を保持する。
使われ方：元評価同型を保つ全実 gluing cone 比較の指定包含面。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type w} [DGCategory R P]
  (F G F' G' : DGFunctor R P (RightModule R D))
  (α : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (β : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F' G')
  (l : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F F') (r : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans G G')
  (hsq : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp α r = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp l β)
include hsq
local notation "f" => dgModuleNaturalConeArrow R D F G α
local notation "g" => dgModuleNaturalConeArrow R D F' G' β
local notation "a" => dgModuleNaturalConeArrow R D F F' l
local notation "b" => dgModuleNaturalConeArrow R D G G' r


local notation "CA" => dgModuleNaturalConeFunctor R D F G α
local notation "CB" => dgModuleNaturalConeFunctor R D F' G' β
local notation "ι" => dgModuleNaturalConeInr R D F' G' β
local notation "ξ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp r (ι)
local notation "s" => dgModuleNaturalConePrecompositionInput R D F F' G' l β


local notation "θ" => dgModuleNaturalConeSquare R D F G F' G' α β l r hsq

/-- 概要：元 cone square 全比較の包含制限は指定右辺と元包含の全合成。
方針：元全 descent の包含式と閉射回収を使う。
規約：全厳密比較の等号。使われ方：実 gluing cone の指定境界。 -/
lemma dgModuleNaturalConeSquare_inr :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (dgModuleNaturalConeInr R D F G α) (θ) = (ξ) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_ext
  intro x
  apply (closedHomEquiv R (RightModule R D) (G.obj x) ((CB).obj x)).symm.injective
  change dgModuleNaturalConeArrow R D G (CB)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (dgModuleNaturalConeInr R D F G α) (θ)) x =
    dgModuleNaturalConeArrow R D G (CB) (ξ) x
  rw [dgModuleNaturalConeArrow_comp, dgModuleNaturalConeInr_arrow]
  exact dgModuleNaturalConeDesc_inr R D F G (CB) α (ξ) (s)
    (dgModuleNaturalConeSquare_boundary R D F G F' G' α β l r hsq)
    (dgModuleNaturalConePrecompositionInput_naturality R D F F' G' l β) x
end SerrePositivity.KST.SConstruction
