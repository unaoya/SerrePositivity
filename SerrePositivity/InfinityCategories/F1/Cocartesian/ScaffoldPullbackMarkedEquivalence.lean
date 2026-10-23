module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldPullbackMarked
public import SerrePositivity.InfinityCategories.F1.MarkedCocartesianFunctorRestrictionLifting
public import SerrePositivity.InfinityCategories.F1.FullSubcomplexRestrictionEquivalence

/-!
概要：任意の部分底で、元の辺保存 Hom の同じ scaffold 前合成は同値。
方針：全相対 Hom の同値を、同型不変で反映される実際の辺保存条件へ制限する。
規約：部分底は任意の単体集合でよく、scaffold の像だけへの分類ではない。
使われ方：境界上の native Hom の実際の scaffold 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] {E F : SSet.{u}}
  (p : E ⟶ nerve C) (q : F ⟶ nerve C) (a : Over (nerve C))

local instance [InnerFibration q] : Quasicategory (cocartesianPullbackHomSpace p q a) :=
  inferInstanceAs (Quasicategory (markedCocartesianFunctorSpace q
    (pullback.snd a.hom p ≫ p) {e | IsCocartesianEdge (pullback.fst a.hom p) e}))

local instance [InnerFibration q] :
    Quasicategory (cocartesianScaffoldPullbackMarkedHom p q a) :=
  inferInstanceAs (Quasicategory (markedCocartesianFunctorSpace q _
    (cocartesianScaffoldPullbackMark p a)))

/-- 部分底上の同じ辺保存前合成は、全相対 Hom の比較を厳密に制限する。 -/
lemma cocartesianScaffoldPullbackMarkedPre_ι :
    cocartesianScaffoldPullbackMarkedPre p q a ≫
      markedCocartesianFunctorInclusion q
        (pullback.snd a.hom
          (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p)) ≫
            simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p))
        (cocartesianScaffoldPullbackMark p a) =
      markedCocartesianFunctorInclusion q (pullback.snd a.hom p ≫ p)
        {e | IsCocartesianEdge (pullback.fst a.hom p) e} ≫
          cocartesianScaffoldPullbackRawHomPre p q a :=
  markedCocartesianFunctorPre_ι q (cocartesianScaffoldPullbackOverMap p a) _ _ _

/-- 元の辺保存 Hom の同じ scaffold 前合成は、任意の部分底で同値。 -/
lemma cocartesianScaffoldPullbackMarkedPre_isQCatEquivalence
    [CocartesianFibration p] [CocartesianFibration q] :
    IsQCatEquivalence (cocartesianScaffoldPullbackMarkedPre p q a) := by
  apply isQCatEquivalence_fullSubcomplexRestriction
    (markedCocartesianFunctorPredicate q (pullback.snd a.hom p ≫ p)
      {e | IsCocartesianEdge (pullback.fst a.hom p) e})
    (markedCocartesianFunctorPredicate q _ (cocartesianScaffoldPullbackMark p a))
    (fun h ↦ markedCocartesianFunctorPredicate_iff_of_vertexIso q _ _ h)
    (cocartesianScaffoldPullbackRawHomPre p q a)
    (cocartesianScaffoldPullbackRawHomPre_isQCatEquivalence p q a)
    (cocartesianScaffoldPullbackMarkedPre p q a)
    (cocartesianScaffoldPullbackMarkedPre_ι p q a)
  exact cocartesianScaffoldPullbackMarkedPredicate_reflect p q a

/-- 元の辺保存 Hom の core 上で作用する、同じ scaffold 前合成。 -/
def cocartesianScaffoldPullbackMarkedCorePre :=
  quasicategoryCoreMap (cocartesianScaffoldPullbackMarkedPre p q a)

/-- 同じ辺保存 core の比較も、部分底の充填性を仮定せず同値。 -/
lemma cocartesianScaffoldPullbackMarkedCorePre_isQCatEquivalence
    [CocartesianFibration p] [CocartesianFibration q] :
    IsQCatEquivalence (cocartesianScaffoldPullbackMarkedCorePre p q a) :=
  (cocartesianScaffoldPullbackMarkedPre_isQCatEquivalence p q a).core

end SerrePositivity.InfinityCategories
