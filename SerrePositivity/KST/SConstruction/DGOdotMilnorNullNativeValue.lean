module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingNullPerfectEquivalence
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisIdentityNative

/-!
概要：元実零化始域 V の native 値と固定 ν 値を、元包含辺の全比較付きで接続する。
方針：元対角因子化の準同値で前三角性を運び、同じ Yoneda の自然性を適用する。
規約：同じ V・元包含・元 native 比較を保持し、三認証の完成とは区別する。
使われ方：共通実長方形の右面を恒等 lax 面へ全比較するための始域境界。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories LocalizingInvariants

variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "U" => DGOdotMilnorRightAxisBase R d
local notation "V" => DGIdentityHomGluingNullDomain R (U)
local notation "L" => DGIdentityHomGluing R (U)

/-- 概要：元実零化始域 V の前三角性は無条件で充足する。
方針：元逆回転基底の前三角性を同じ対角因子化の準同値で運ぶ。
規約：元小基底を保持。使われ方：固定 ν の実 V 比較。 -/
lemma dgOdotMilnorNullDomain_pretriangulated : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (V) := by
  letI := dgOdotMilnorRightAxisBase_pretriangulated R d
  exact dgIdentityHomGluingNullDomain_pretriangulated R (U)

/-- 概要：元実零化始域 V の native nerve は coherent 冪等完備。
方針：元基底の完備性を同じ native 指定同値で運ぶ。
規約：Hom end の自然収縮は使わない。使われ方：元 Yoneda 比較の同値性。 -/
lemma dgOdotMilnorNullDomain_complete : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (V)) :=
  (dgOdotMilnorRightAxisBase_complete R d).of_equivalence
    (dgIdentityHomGluingNullNativeEquivalence R (U))

/-- 概要：同じ V native 値と元固定 ν 頂点の指定同値。
方針：構成済みの元 Yoneda 比較に前三角性と完備性を代入する。
規約：元比較の順方向を保持。使われ方：実右面の始域頂点比較。 -/
def dgOdotMilnorNullNativeValueEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (V))
    (dgKInputStableValue R (dgIdentityHomGluingNullInput R (U))).obj :=
  (@dgKNativeValueComparison_isQCatEquivalence R _ (V) _ _
    (dgOdotMilnorNullDomain_pretriangulated R d)
    (dgOdotMilnorNullDomain_complete R d)).choose

/-- 概要：V の元包含の native 全辺と同じ固定 ν 辺は全自然に可換。
方針：元二頂点の Yoneda 指定同値に同じ dg 包含の自然性を適用する。
規約：同じ元包含と全関手同型を保持。使われ方：実右面の指定包含境界。 -/
def dgOdotMilnorNullInclusionNuComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorNullNativeValueEquivalence R d).hom ≫
      (dgKInputNuMap R (dgIdentityHomGluingNullInputMap R (U))).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgIdentityHomGluingNullInclusion R (U)) ≫
      (dgOdotMilnorRightAxisTargetNativeValueEquivalence R d).hom) :=
  @dgKNativeNuNaturality R _ (V) (L) _ _
    (dgOdotMilnorNullDomain_pretriangulated R d) _ _
    (dgOdotMilnorRightAxisTarget_pretriangulated R d)
    (dgIdentityHomGluingNullInclusion R (U))

/-- 概要：元対角因子化の native 全辺と固定 ν 辺は全自然に可換。
方針：元逆回転基底と V の同じ Yoneda 比較に自然性を適用する。
規約：元 strict 対角の V 因子化を保持。使われ方：実右面の元対角境界比較。 -/
def dgOdotMilnorNullDiagonalNuComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorRightAxisIdentityBaseNativeValueEquivalence R d).hom ≫
      (dgKInputNuMap R (dgIdentityHomGluingDiagonalNullFactorInputMap R (U))).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgIdentityHomGluingDiagonalNullFactor R (U)) ≫
      (dgOdotMilnorNullNativeValueEquivalence R d).hom) :=
  @dgKNativeNuNaturality R _ (U) (V) _ _
    (dgOdotMilnorRightAxisBase_pretriangulated R d) _ _
    (dgOdotMilnorNullDomain_pretriangulated R d)
    (dgIdentityHomGluingDiagonalNullFactor R (U))

/-- 概要：共通実右面に使う元対角因子化の固定 ν 辺は無条件で同値。
方針：元逆回転基底の前三角性を実因子化の準同値へ代入する。
規約：同じ元入力辺。使われ方：絶対恒等面から V 実面への始域比較。 -/
lemma dgOdotMilnorNullDiagonalNu_isQCatEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
    (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
      (dgKInputStableValue R (dgIdentityHomGluingBaseInput R (U)))
      (dgKInputStableValue R (dgIdentityHomGluingNullInput R (U))) from
      dgKInputNuMap R (dgIdentityHomGluingDiagonalNullFactorInputMap R (U))).hom := by
  letI := dgOdotMilnorRightAxisBase_pretriangulated R d
  exact dgIdentityHomGluingDiagonalNullFactorInputMap_nu_equivalence R (U)

end SerrePositivity.KST.SConstruction
