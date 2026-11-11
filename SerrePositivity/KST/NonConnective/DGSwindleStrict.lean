module

public import SerrePositivity.KST.NonConnective.DGSwindleEnriched
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNatTransUnitNaturality
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations

/-!
概要：構成した swindle を、全斉次射に自然な厳密 dg 自然変換へ束ねる。
方針：元の実閉同型と全 Hom の自然性を使用し、逆向きも同じ閉同型から構成する。
規約：成分は元の実閉射の cycle そのもの。存在だけの自然同型に置き換えない。
使われ方：明示入力の κ-compact dg cone への swindle の制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

/-- 同じ閉 dg swindle 射を成分とする、全斉次射に自然な厳密 dg 変換。 -/
def dgSwindleStrictHom :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (dgSwindleSourceFunctor R D) (dgCountableSumFunctor R D) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransOfUnitNaturality
    (F := dgSwindleSourceFunctor R D) (G := dgCountableSumFunctor R D)
    (fun M ↦ eHomEquiv (_root_.SerrePositivity.DifferentialGraded.Complex R) (countableSwindleIso (_root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) M).hom)
    (by
      intro M N
      simpa only [eHomWhiskerLeft, eHomWhiskerRight, Category.assoc,
        countableSwindleIso, dgCountableSumFunctor, _root_.SerrePositivity.DifferentialGraded.homObject,
        dgSwindleSourceFunctor_obj,
        countableSumObject, dgCountableSumObj] using
        dgSwindleHom_enriched_naturality R D M N)

/-- 同じ実閉 swindle 同型の逆射も、全 Hom chain map に関して自然。 -/
lemma dgSwindleInv_enriched_naturality (M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) :
    dgCountableSumHom R D M N ≫ eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (dgCountableSumObj R D M) (countableSwindleIso (_root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) N).inv =
    (dgSwindleSourceFunctor R D).map M N ≫ eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (countableSwindleIso (_root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) M).inv ((dgSwindleSourceFunctor R D).obj N) :=
  _root_.SerrePositivity.DifferentialGraded.moduleHom_iso_square_inv R D _ _ (countableSwindleIso (_root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) M)
    (countableSwindleIso (_root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) N) (dgSwindleHom_enriched_naturality R D M N)

/-- 同じ閉 dg swindle の逆射を成分とする厳密 dg 自然変換。 -/
def dgSwindleStrictInv :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (dgCountableSumFunctor R D) (dgSwindleSourceFunctor R D) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransOfUnitNaturality
    (F := dgCountableSumFunctor R D) (G := dgSwindleSourceFunctor R D)
    (fun M ↦ eHomEquiv (_root_.SerrePositivity.DifferentialGraded.Complex R) (countableSwindleIso (_root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) M).inv)
    (by
      intro M N
      simpa only [eHomWhiskerLeft, eHomWhiskerRight, Category.assoc,
        countableSwindleIso, dgCountableSumFunctor, _root_.SerrePositivity.DifferentialGraded.homObject,
        dgSwindleSourceFunctor_obj,
        countableSumObject, dgCountableSumObj] using
        dgSwindleInv_enriched_naturality R D M N)

end SerrePositivity.KST.NonConnective
