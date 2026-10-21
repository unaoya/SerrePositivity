module

public import SerrePositivity.InfinityCategories.F1.IntervalMappingPostEquivalence
public import SerrePositivity.InfinityCategories.Core.EquivalencePathFinalLifting

/-!
概要：同じ可逆 path の Hom の両端評価を、元の二つの Hom の共通比較として使う。
方針：可逆 path の両端の全境界持ち上げを、端点固定の区間 Hom へ移す。
規約：同じ path の全 Hom と実際の後合成を使う。
使われ方：底変換比較の両側の Hom 作用を、全パラメーターで厳密に比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {A Y : SSet.{u}} (P : A ⟶ equivalencePath Y) (i : Fin 2) (a b : A _⦋0⦌)
  {a' b' : Y _⦋0⦌} (ha : (P ≫ equivalencePathEndpoint Y i).app _ a = a')
  (hb : (P ≫ equivalencePathEndpoint Y i).app _ b = b')

/-- 同じ path の Hom を元の端点の Hom へ評価し、指定した端点へ正規化する。 -/
def intervalHomPathEndpoint :
    intervalMappingSpace (P.app _ a) (P.app _ b) ⟶ intervalMappingSpace a' b' :=
  intervalMappingPostOfEq (equivalencePathEndpoint Y i) (P.app _ a) (P.app _ b) ha hb

/-- 同じ Hom の端点評価は、展開した元の区間族への端点の後合成。 -/
lemma intervalHomPathEndpoint_uncurry {T : SSet.{u}}
    (s : T ⟶ intervalMappingSpace (P.app _ a) (P.app _ b)) :
    intervalMappingUncurry (s ≫ intervalHomPathEndpoint P i a b ha hb) =
      intervalMappingUncurry s ≫ equivalencePathEndpoint Y i :=
  intervalMappingPostOfEq_uncurry _ _ _ _ _ s

/-- 同じ path を経由した区間 Hom の作用は、元の端点での同じ作用を厳密に回収する。 -/
lemma intervalHomPathEndpoint_factor :
    intervalMappingPost P a b ≫ intervalHomPathEndpoint P i a b ha hb =
      intervalMappingPostOfEq (P ≫ equivalencePathEndpoint Y i) a b ha hb := by
  apply intervalMappingUncurry_injective
  rw [intervalHomPathEndpoint_uncurry, intervalMappingPost_universal_uncurry]
  have h := intervalMappingPostOfEq_uncurry
    (P ≫ equivalencePathEndpoint Y i) a b ha hb (𝟙 _)
  rw [Category.id_comp] at h
  rw [h, Category.assoc]

/-- 同じ path の Hom の各端点評価は、実際の全境界の持ち上げを持つ。 -/
lemma intervalHomPathEndpoint_trivialKanFibration [Quasicategory Y] :
    TrivialKanFibration (intervalHomPathEndpoint P i a b ha hb) := by
  fin_cases i
  · exact intervalMappingPostOfEq_trivialKanFibration
      (equivalencePathEndpoint Y 0) (P.app _ a) (P.app _ b) ha hb
  · exact intervalMappingPostOfEq_trivialKanFibration
      (equivalencePathEndpoint Y 1) (P.app _ a) (P.app _ b) ha hb

/-- 同じ path の Hom の各端点評価そのものは、元の Hom の同値。 -/
lemma intervalHomPathEndpoint_isQCatEquivalence [Quasicategory Y] :
    IsQCatEquivalence (intervalHomPathEndpoint P i a b ha hb) := by
  have := intervalHomPathEndpoint_trivialKanFibration P i a b ha hb
  exact isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories
