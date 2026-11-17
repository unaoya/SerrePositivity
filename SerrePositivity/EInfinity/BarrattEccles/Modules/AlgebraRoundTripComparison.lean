module

public import SerrePositivity.EInfinity.Modules.RelativeNaturalComparison
public import SerrePositivity.EInfinity.BarrattEccles.Modules.AlgebraModelComparison

/-!
# 同じ BE 底の模型の往復と正則加群の射影の全比較

概要：HA §4.2.3 の同じ底の包含・置換の指定弱比較を全関手間に移す。
方針：元の弱自然変換の円筒を局所化し、正則加群の射影公式と貼り合わせる。
規約：元の二つの実関手を保つ。単なる対象ごとの同値ではない。
使われ方：同じ全加群族の単位の底を恒等と比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.EInfinity.Modules _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable (A : Type u) [CommRing A]

/-- 概要：同じ cofibrant 底の往復を恒等と比較する（HA §4.2.3）。
方針：元の指定弱比較の円筒を局所化する。
規約：全関手単体集合での同型。使われ方：同じ底の模型の単位。 -/
def cAlgModelRoundTripIso :
    FunctorIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (cofibrantToAlgebraDKRelative A) ≫
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (algebraToCofibrantDKRelative A)) (𝟙 (CAlg_R A)) := by
  have h := localizationNerveMapIsoOfWeakNatTrans
    (F := cofibrantToAlgebraDKRelative A ≫ algebraToCofibrantDKRelative A)
    (G := 𝟙 (cofibrantAlgebraRelativeCategory A))
    (cofibrantDKComparison A) (cofibrantDKComparison_weak A)
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap_comp, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap_id] at h
  exact h

/-- 概要：同じ全代数底の往復を恒等と比較する（HA §4.2.3）。
方針：元の指定弱比較の円筒を局所化する。
規約：全関手単体集合での同型。使われ方：同じ底の模型の余単位。 -/
def algebraModelRoundTripIso :
    FunctorIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (algebraToCofibrantDKRelative A) ≫
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (cofibrantToAlgebraDKRelative A))
      (𝟙 (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerve (algebraRelativeCategory A))) := by
  have h := localizationNerveMapIsoOfWeakNatTrans
    (F := algebraToCofibrantDKRelative A ≫ cofibrantToAlgebraDKRelative A)
    (G := 𝟙 (algebraRelativeCategory A))
    (algebraDKComparison A) (algebraDKComparison_weak A)
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap_comp, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap_id] at h
  exact h

/-- 概要：同じ包含・置換を実際の逆関手とする底の同値（HA §4.2.3）。
方針：元の両往復の全比較を束ねる。
規約：別の逆関手を選び直さない。使われ方：同じ加群族の底の比較。 -/
def cAlgAlgebraModelEquivalence :
    QCatEquivalence (CAlg_R A) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerve (algebraRelativeCategory A)) where
  hom := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (cofibrantToAlgebraDKRelative A)
  inv := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (algebraToCofibrantDKRelative A)
  homInvIso := cAlgModelRoundTripIso A
  invHomIso := algebraModelRoundTripIso A

/-- 概要：同じ正則加群の実関手の射影を恒等と比較する（HA §4.2.3）。
方針：元の全単体の射影公式に同じ底の往復比較を貼る。
規約：全関手間の可逆比較。使われ方：単位の section の底の回収。 -/
def moduleUnitSection_projectionIso :
    FunctorIso (moduleUnitSection A ≫ moduleTotalProjection A) (𝟙 (CAlg_R A)) := by
  rw [moduleUnitSection_projection, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap_comp]
  exact cAlgModelRoundTripIso A

end SerrePositivity.EInfinity.BarrattEccles
