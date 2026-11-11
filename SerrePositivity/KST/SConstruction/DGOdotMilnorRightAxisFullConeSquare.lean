module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeFullSquare
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisFullConeTriangle

/-!
概要：元 Milnor 右軸比較の同じ cone 全四角形と全関手 cofiber 列を保持する。
方針：元実商延長の同じ厳密変換を構成済みの全 cone 図式へ代入する。
規約：元解像度・実商・指定全零化二単体と実零角を保持する。
使われ方：元 LT counit の逆回転と固定 ν の中央比較への接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet DifferentialGraded InfinityCategories
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "P" => DGCategoryCellResolution.Source R (DGOdotGluing R d)
local notation "Q" => DGQuotient.QuotientObject (P)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGOdotGluing R d)
    (dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))))
local notation "I" => perfectDGModuleInclusion R (Q) Set.univ
local notation "F" => DGFunctor.comp (dgOdotMilnorRightAxisQuotientSource R d) (I)
local notation "G" => DGFunctor.comp (dgOdotMilnorRightAxisQuotientTarget R d) (I)
local notation "η" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp
  (dgOdotMilnorRightAxisQuotientStrictNatTrans R d) (I)

/-- 概要：元実商上の右軸比較の同じ全関手 cone 四角形。
方針：同じ元厳密変換を全 cone 図式へ特殊化。
規約：元全 Hom と元零化面を保持。使われ方：元全逆回転の cofiber 比較。 -/
def dgOdotMilnorRightAxisFullConeSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶
      (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (P))).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R (Q))) :=
  dgModuleNaturalConeFullSquare R (Q) (P) (F) (G) (η)

/-- 概要：同じ元全四角形の下二単体は保存済み指定零化面そのもの。
方針：元全評価の下二単体回収を特殊化する。
規約：元次数 −1 全族を保持。使われ方：元指定面の同時比較。 -/
lemma dgOdotMilnorRightAxisFullConeSquare_lower :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ dgOdotMilnorRightAxisFullConeSquare R d =
      SSet.yonedaEquiv.symm (dgOdotMilnorRightAxisFullConeTriangle R d) :=
  dgModuleNaturalConeFullSquare_lower R (Q) (P) (F) (G) (η)

/-- 概要：元実商上の右軸比較の全 cone 図式を同じ零角付きで保持する。
方針：元全零角付き図式へ特殊化する。
規約：同じ実零加群を使用。使われ方：元全 cofiber 列。 -/
def dgOdotMilnorRightAxisFullConeZeroTriangle :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (P))).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R (Q)))) :=
  dgModuleNaturalConeFullZeroTriangle R (Q) (P) (F) (G) (η)

/-- 概要：元右軸比較の同じ全 cone 図式は実 cofiber 列。
方針：元全 cofiber の証明を同じ入力に特殊化する。
規約：追加主仮定なし。使われ方：元逆回転の全図式比較。 -/
lemma dgOdotMilnorRightAxisFullConeZeroTriangle_isCofiber :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence (dgOdotMilnorRightAxisFullConeZeroTriangle R d) :=
  dgModuleNaturalConeFullZeroTriangle_isCofiber R (Q) (P) (F) (G) (η)

end SerrePositivity.KST.SConstruction
