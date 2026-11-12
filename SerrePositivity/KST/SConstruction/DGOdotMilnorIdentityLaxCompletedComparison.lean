module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorIdentityLaxBaseChange
public import SerrePositivity.KST.SConstruction.DGOdotMilnorLaxComparisonRequest

/-!
概要：D2 の恒等 lax 全比較を、同じ元 resolved 商の完備化先へ接続する。
方針：構成済み基底変更の対角等号・実差全同型と供給入力の二辺比較を合成する。
規約：D2 入力の存在は未証明。実右面や全 LT 長方形の存在証明とは数えない。
使われ方：供給された同じ全比較から LT 右面の指定二境界を回収する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable {R : Type u} [CommRing R] {d : DGOdotInput R}
namespace DGOdotMilnorIdentityLaxComparisonInput
variable (v : DGOdotMilnorIdentityLaxComparisonInput R d)
local notation "C" => dgKInputStableValue R (dgOdotMilnorIdentityBaseInput R d)
local notation "Q" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "e" => dgOdotMilnorIdentityBaseValueEquivalence R d

/-- 概要：供給比較を元 resolved 商の同じ恒等 lax 圏へ運ぶ。
方針：既存の実基底変更を後合成する。規約：供給入力の存在は仮定。
使われ方：実右面の中央頂点の全比較。 -/
def completedGluing : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (dgKInputStableValue R (dgOdotMilnorIdentityGluingInput R d)).obj
    (laxCategory (𝟙 (Q)) (𝟙 (Q))).obj :=
  v.gluing.trans (dgOdotMilnorIdentityLaxBaseChange R d)

/-- 概要：元固定 ν 対角を、同じ完備化先の恒等対角へ全関手同型で照合する。
方針：供給の全対角比較と基底変更の対角等号を合成する。
規約：元の始域値同値を保持。使われ方：右面の指定包含比較。 -/
def completedDiagonal : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgKInputNuMap R (dgOdotMilnorIdentityDiagonalInputMap R d)).hom ≫
      v.completedGluing.hom)
    ((e).hom ≫ (IdentityLax.exactDiagonal (Q)).hom) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    (v.diagonal.postcomp (dgOdotMilnorIdentityLaxBaseChange R d).hom)
    (Category.assoc _ _ _) (dgOdotMilnorIdentityLaxBaseChange_diagonal R d)

/-- 概要：元固定 ν 差を、同じ完備化先の恒等 lax 差へ全関手同型で照合する。
方針：基底変更の cofiber 完全自然性と供給の実 cone 比較を合成する。
規約：同じ指定終域比較を保持。使われ方：右面の指定商比較。 -/
def completedDifference : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (v.completedGluing.hom ≫ (exactLaxDifference (𝟙 (Q)) (𝟙 (Q))).hom)
    ((dgKInputNuMap R (dgOdotMilnorIdentityDifferenceInputMap R d)).hom ≫
      (v.difference.hom ≫ (e).hom)) := by
  have a := (dgOdotMilnorIdentityLaxBaseChange_difference R d).precomp v.gluing.hom
  have b := v.cone.postcomp (e).hom
  have t := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq a (Category.assoc _ _ _).symm
    (Category.assoc _ _ _).symm).trans b
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq t rfl (Category.assoc _ _ _)
end DGOdotMilnorIdentityLaxComparisonInput
end SerrePositivity.KST.SConstruction
