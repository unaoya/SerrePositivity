module

public import SerrePositivity.KST.NonConnective.DGSumFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNatTransUnitNaturality

/-!
概要：同じ dg 関手族の実直和への、全斉次射に自然な元の注入。
方針：全 Hom の余積普遍性の射影公式を、そのまま厳密 dg 自然変換へ移す。
規約：零次自然性だけでは代用しない。
使われ方：swindle の分裂 cofiber 族と固定 Perf 作用への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {C : Type w} [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] {J : Type t} [Small.{u} J]
  (F : J → _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.ModuleCategory R D))

/-- 直和への指定注入を成分とする、元の全斉次自然変換。 -/
def dgSumFamilyStrictInclusion (j : J) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (F j) (dgSumFamilyFunctor R D F) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransOfUnitNaturality
    (F := F j) (G := dgSumFamilyFunctor R D F)
    (fun X ↦ eHomEquiv (_root_.SerrePositivity.DifferentialGraded.Complex R) (Sigma.ι (fun j ↦ (F j).obj X) j)) (by
      intro X Y
      simpa only [eHomWhiskerLeft, eHomWhiskerRight, Category.assoc,
        dgSumFamilyFunctor, _root_.SerrePositivity.DifferentialGraded.homObject] using
        (dgSumFamilyHom_injection R D F X Y j).symm)

/-- 各成分は同じ実余積注入の閉 cycle。 -/
lemma dgSumFamilyStrictInclusion_app (j : J) (X : C) :
    (dgSumFamilyStrictInclusion R D F j).app X =
      _root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (eHomEquiv (_root_.SerrePositivity.DifferentialGraded.Complex R) (Sigma.ι (fun j ↦ (F j).obj X) j)) := rfl

end SerrePositivity.KST.NonConnective
