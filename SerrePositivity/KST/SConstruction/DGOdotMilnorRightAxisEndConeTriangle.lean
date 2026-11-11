module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeEndTriangle
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisSmallArrow

/-!
概要：元 Milnor 右軸比較の同じ実商延長に対する cone 零化面を全関手 end に保持する。
方針：元実 Perf 厳密変換を同じ加群包含で後合成し、構成した end 二単体へ代入する。
規約：元解像度・実商・元比較・元 cone 左包含を変更しない。
使われ方：元 counit の全矢印族と実逆回転の固定 ν 比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
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

/-- 概要：元実右軸比較の cone 零化を、同じ全加群関手圏の実二単体で保持する。
方針：元厳密比較と元包含をそのまま end の cone 面に代入する。
規約：対象別の零化の選択なし。元全 Hom と次数 −1 成分を保持。
使われ方：元実逆回転を cofiber 図式の全族へ接続する。 -/
def dgOdotMilnorRightAxisEndConeTriangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (DGFunctor R (P) (RightModule R (Q))) 2 :=
  dgModuleNaturalConeEndTriangle R (Q) (F) (G) (η)

end SerrePositivity.KST.SConstruction
