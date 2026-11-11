module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityHomTargetLaxEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityLaxArrowBase
public import SerrePositivity.KST.SConstruction.DGOdotMilnorIdentityValueEquivalences
public import SerrePositivity.KST.SConstruction.DGOdotMilnorLaxComparisonRequest
/-!
概要：恒等 Hom gluing の全比較を、同じ固定入力の中央同値へ特殊化する。
方針：元の native 比較を指定 ν 同値で挟み、恒等二脚の基底を移す。
規約：対角・cone 欄の完成とは区別する。使われ方：恒等比較入力の gluing 欄。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory SSet DifferentialGraded KST.SConstruction
open _root_.SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "C" => DGOdotMilnorIdentityBase R d
local notation "L" => DGOdotMilnorIdentityGluing R d
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C := dgOdotMilnorIdentityBase_pretriangulated R d
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R L := dgOdotMilnorIdentityGluing_pretriangulated R d

def dgGluingIdentityInputLaxEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (dgKInputStableValue R (dgOdotMilnorIdentityGluingInput R d)).obj
      (laxCategory (𝟙 (dgKInputStableValue R (dgOdotMilnorIdentityBaseInput R d)))
        (𝟙 (dgKInputStableValue R (dgOdotMilnorIdentityBaseInput R d)))).obj :=
  (dgOdotMilnorIdentityGluing_nu_equivalence R d).choose.symm.trans
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityHomTargetLaxEquivalence.{u, 0} R C).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.identityLaxArrowBaseEquivalence (dgOdotMilnorIdentityBase_nu_equivalence R d).choose))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
