module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxCospanCofiberComparison
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackCospanIsoEquivalence
public import SerrePositivity.InfinityCategories.Stable.EquivalenceStability
/-!
概要：全関手同型で可換な cospan の指定全比較は、選択 cofiber 差と全関手同型で可換する。
方針：可逆 path 置換上の二厳密比較の cofiber 自然性を、同じ逆と往復則で合成する。
規約：指定 cospan 比較を取り替えない。使われ方：元 corner の全 cone 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.KST.LocalizingInvariants
open scoped _root_.Simplicial
variable {A B C A' B' C' : SSet.{u}}
  [Quasicategory A] [Quasicategory B] [Quasicategory C]
  [Quasicategory A'] [Quasicategory B'] [Quasicategory C'] [IsStable C] [IsStable C']
  (p : A ⟶ C) (q : B ⟶ C) (p' : A' ⟶ C') (q' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (hp : FunctorIso (p ≫ c) (a ≫ p')) (hq : FunctorIso (q ≫ c) (b ≫ q'))
  (ha : IsQCatEquivalence a) (hb : IsQCatEquivalence b) (hc : IsQCatEquivalence c)
local notation "P" => F2.cospanPathLeg p p' a c hp
local notation "Q" => F2.cospanPathLeg q q' b c hq

def laxCospanIsoCofiberComparison : FunctorIso
    ((F2.laxPullbackCospanIsoEquivalence p q p' q' a b c hp hq ha hb hc).hom ≫
      _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber C' (F2.laxPullbackArrow p' q'))
    (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber C (F2.laxPullbackArrow p q) ≫ c) := by
  let π := equivalencePathReplacementProjection c
  let γ := equivalencePathReplacementMap c
  have hπ : IsQCatEquivalence π := isQCatEquivalence_of_trivialKanFibration π
  have hγ : IsQCatEquivalence γ := (isQCatEquivalence_iff_equivalencePathReplacementMap c).mp hc
  letI : IsStable (equivalencePathReplacement c) := hπ.choose.isStable_iff.mpr inferInstance
  letI : IsExactFunctor π := isExactFunctor_of_isQCatEquivalence hπ
  letI : IsExactFunctor γ := isExactFunctor_of_isQCatEquivalence hγ
  let e := F2.cospanPathLaxProjectionEquivalence p q p' q' a b c hp hq
  let t := F2.cospanPathLaxTarget p q p' q' a b c hp hq
  let dm := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber (equivalencePathReplacement c) (F2.laxPullbackArrow P Q)
  let d₀ := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber C (F2.laxPullbackArrow p q)
  let d₁ := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber C' (F2.laxPullbackArrow p' q')
  have h₀ : FunctorIso (e.hom ≫ d₀) (dm ≫ π) :=
    laxCospanCofiberComparison P Q p q (equivalencePathReplacementProjection a)
      (equivalencePathReplacementProjection b) π
      (F2.cospanPathLeg_projection p p' a c hp) (F2.cospanPathLeg_projection q q' b c hq)
  have h₁ : FunctorIso (t ≫ d₁) (dm ≫ γ) :=
    laxCospanCofiberComparison P Q p' q' (equivalencePathReplacementMap a)
      (equivalencePathReplacementMap b) γ
      (F2.cospanPathLeg_map p p' a c hp) (F2.cospanPathLeg_map q q' b c hq)
  have k₁ : FunctorIso (e.inv ≫ t ≫ d₁) (e.inv ≫ dm ≫ γ) := by
    simpa only [FunctorIso, Category.assoc] using h₁.precomp e.inv
  have k₂ : FunctorIso (e.inv ≫ dm ≫ γ) (e.inv ≫ dm ≫ π ≫ c) := by
    simpa only [FunctorIso, Category.assoc] using
      FunctorIso.precomp (equivalencePathReplacementFunctorIso c).symm (e.inv ≫ dm)
  have k₃ : FunctorIso (e.inv ≫ dm ≫ π ≫ c) (e.inv ≫ e.hom ≫ d₀ ≫ c) := by
    simpa only [FunctorIso, Category.assoc] using
      (FunctorIso.precomp h₀.symm e.inv).postcomp c
  have k₄ : FunctorIso (e.inv ≫ e.hom ≫ d₀ ≫ c) (d₀ ≫ c) := by
    simpa only [FunctorIso, Category.assoc, Category.id_comp] using e.invHomIso.postcomp (d₀ ≫ c)
  exact F2.functorIsoOfEq (k₁.trans (k₂.trans (k₃.trans k₄))) (Category.assoc _ _ _).symm rfl

end SerrePositivity.InfinityCategories
