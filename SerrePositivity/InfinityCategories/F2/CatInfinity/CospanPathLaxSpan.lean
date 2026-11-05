module
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CospanPathLeg
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackCospanEquivalence
/-!
概要：全関手同型で可換な cospan 比較を、可逆 path 置換上の二つの厳密 lax 比較へ移す。
方針：元への射影と比較先への終点を保持する脚を使い、成分同値判定を適用する。
規約：元の入力比較を選び直さない。使われ方：固定 ν の二脚への全比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.F2
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
variable {A B C A' B' C' : SSet.{u}}
  [Quasicategory A] [Quasicategory B] [Quasicategory C]
  [Quasicategory A'] [Quasicategory B'] [Quasicategory C']
  (p : A ⟶ C) (q : B ⟶ C) (p' : A' ⟶ C') (q' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (hp : FunctorIso (p ≫ c) (a ≫ p')) (hq : FunctorIso (q ≫ c) (b ≫ q'))
local notation "P" => cospanPathLeg p p' a c hp
local notation "Q" => cospanPathLeg q q' b c hq

def cospanPathLaxProjection : laxPullback P Q ⟶ laxPullback p q :=
  laxPullbackCospanMap P Q p q (equivalencePathReplacementProjection a)
    (equivalencePathReplacementProjection b) (equivalencePathReplacementProjection c)
    (cospanPathLeg_projection p p' a c hp) (cospanPathLeg_projection q q' b c hq)

lemma cospanPathLaxProjection_isQCatEquivalence :
    IsQCatEquivalence (cospanPathLaxProjection p q p' q' a b c hp hq) :=
  laxPullbackCospanMap_isQCatEquivalence P Q p q
    (equivalencePathReplacementProjection a) (equivalencePathReplacementProjection b)
    (equivalencePathReplacementProjection c)
    (cospanPathLeg_projection p p' a c hp) (cospanPathLeg_projection q q' b c hq)
    (isQCatEquivalence_of_trivialKanFibration (equivalencePathReplacementProjection a))
    (isQCatEquivalence_of_trivialKanFibration (equivalencePathReplacementProjection b))
    (isQCatEquivalence_of_trivialKanFibration (equivalencePathReplacementProjection c))

def cospanPathLaxProjectionEquivalence : QCatEquivalence (laxPullback P Q) (laxPullback p q) :=
  (cospanPathLaxProjection_isQCatEquivalence p q p' q' a b c hp hq).choose

def cospanPathLaxTarget : laxPullback P Q ⟶ laxPullback p' q' :=
  laxPullbackCospanMap P Q p' q' (equivalencePathReplacementMap a)
    (equivalencePathReplacementMap b) (equivalencePathReplacementMap c)
    (cospanPathLeg_map p p' a c hp) (cospanPathLeg_map q q' b c hq)

lemma cospanPathLaxTarget_isQCatEquivalence
    (ha : IsQCatEquivalence a) (hb : IsQCatEquivalence b) (hc : IsQCatEquivalence c) :
    IsQCatEquivalence (cospanPathLaxTarget p q p' q' a b c hp hq) :=
  laxPullbackCospanMap_isQCatEquivalence P Q p' q'
    (equivalencePathReplacementMap a) (equivalencePathReplacementMap b)
    (equivalencePathReplacementMap c)
    (cospanPathLeg_map p p' a c hp) (cospanPathLeg_map q q' b c hq)
    ((isQCatEquivalence_iff_equivalencePathReplacementMap a).mp ha)
    ((isQCatEquivalence_iff_equivalencePathReplacementMap b).mp hb)
    ((isQCatEquivalence_iff_equivalencePathReplacementMap c).mp hc)

end SerrePositivity.InfinityCategories.F2
