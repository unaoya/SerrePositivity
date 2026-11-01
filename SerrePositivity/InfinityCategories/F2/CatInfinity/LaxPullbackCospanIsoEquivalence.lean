module
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CospanPathLaxSpan
public import SerrePositivity.InfinityCategories.Core.FunctorIsoTransport
/-!
概要：全関手同型で可換な cospan の三成分同値から、元二射影を保つ全 lax 比較を構成する。
方針：可逆 path 置換上の二厳密比較を合成し、元の入力 path と逆の往復同型で射影を回収する。
規約：指定三成分と二つの全関手同型を保持する。使われ方：固定 ν 二脚への比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.F2
open CategoryTheory Limits SSet
open scoped Simplicial
variable {A B C A' B' C' : SSet.{u}}
  [Quasicategory A] [Quasicategory B] [Quasicategory C]
  [Quasicategory A'] [Quasicategory B'] [Quasicategory C']
  (p : A ⟶ C) (q : B ⟶ C) (p' : A' ⟶ C') (q' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (hp : FunctorIso (p ≫ c) (a ≫ p')) (hq : FunctorIso (q ≫ c) (b ≫ q'))
  (ha : IsQCatEquivalence a) (hb : IsQCatEquivalence b) (hc : IsQCatEquivalence c)
local notation "P" => cospanPathLeg p p' a c hp
local notation "Q" => cospanPathLeg q q' b c hq

def laxPullbackCospanIsoEquivalence : QCatEquivalence (laxPullback p q) (laxPullback p' q') :=
  (cospanPathLaxProjectionEquivalence p q p' q' a b c hp hq).symm.trans
    (cospanPathLaxTarget_isQCatEquivalence p q p' q' a b c hp hq ha hb hc).choose

def laxPullbackCospanIsoEquivalence_fst :
    FunctorIso ((laxPullbackCospanIsoEquivalence p q p' q' a b c hp hq ha hb hc).hom ≫
      laxPullbackFst p' q') (laxPullbackFst p q ≫ a) := by
  let e := cospanPathLaxProjectionEquivalence p q p' q' a b c hp hq
  have hπ : e.hom ≫ laxPullbackFst p q =
      laxPullbackFst P Q ≫ equivalencePathReplacementProjection a :=
    laxPullbackCospanMap_fst P Q p q (equivalencePathReplacementProjection a)
      (equivalencePathReplacementProjection b) (equivalencePathReplacementProjection c)
      (cospanPathLeg_projection p p' a c hp) (cospanPathLeg_projection q q' b c hq)
  have hγ : cospanPathLaxTarget p q p' q' a b c hp hq ≫ laxPullbackFst p' q' =
      laxPullbackFst P Q ≫ equivalencePathReplacementMap a :=
    laxPullbackCospanMap_fst P Q p' q' (equivalencePathReplacementMap a)
      (equivalencePathReplacementMap b) (equivalencePathReplacementMap c)
      (cospanPathLeg_map p p' a c hp) (cospanPathLeg_map q q' b c hq)
  have h₂ : FunctorIso
      (e.inv ≫ laxPullbackFst P Q ≫ equivalencePathReplacementMap a)
      (e.inv ≫ laxPullbackFst P Q ≫ equivalencePathReplacementProjection a ≫ a) := by
    simpa only [FunctorIso, Category.assoc] using
      FunctorIso.precomp (equivalencePathReplacementFunctorIso a).symm (e.inv ≫ laxPullbackFst P Q)
  have h₃ : FunctorIso
      (e.inv ≫ laxPullbackFst P Q ≫ equivalencePathReplacementProjection a ≫ a)
      (laxPullbackFst p q ≫ a) := by
    simpa only [FunctorIso, Category.assoc, reassoc_of% hπ, Category.id_comp] using
      e.invHomIso.postcomp (laxPullbackFst p q ≫ a)
  have heq : (laxPullbackCospanIsoEquivalence p q p' q' a b c hp hq ha hb hc).hom ≫
      laxPullbackFst p' q' = e.inv ≫ laxPullbackFst P Q ≫ equivalencePathReplacementMap a := by
    change (e.inv ≫ cospanPathLaxTarget p q p' q' a b c hp hq) ≫ _ = _
    rw [Category.assoc, hγ]
  exact functorIsoOfEq (h₂.trans h₃) heq.symm rfl

def laxPullbackCospanIsoEquivalence_snd :
    FunctorIso ((laxPullbackCospanIsoEquivalence p q p' q' a b c hp hq ha hb hc).hom ≫
      laxPullbackSnd p' q') (laxPullbackSnd p q ≫ b) := by
  let e := cospanPathLaxProjectionEquivalence p q p' q' a b c hp hq
  have hπ : e.hom ≫ laxPullbackSnd p q =
      laxPullbackSnd P Q ≫ equivalencePathReplacementProjection b :=
    laxPullbackCospanMap_snd P Q p q (equivalencePathReplacementProjection a)
      (equivalencePathReplacementProjection b) (equivalencePathReplacementProjection c)
      (cospanPathLeg_projection p p' a c hp) (cospanPathLeg_projection q q' b c hq)
  have hγ : cospanPathLaxTarget p q p' q' a b c hp hq ≫ laxPullbackSnd p' q' =
      laxPullbackSnd P Q ≫ equivalencePathReplacementMap b :=
    laxPullbackCospanMap_snd P Q p' q' (equivalencePathReplacementMap a)
      (equivalencePathReplacementMap b) (equivalencePathReplacementMap c)
      (cospanPathLeg_map p p' a c hp) (cospanPathLeg_map q q' b c hq)
  have h₂ : FunctorIso
      (e.inv ≫ laxPullbackSnd P Q ≫ equivalencePathReplacementMap b)
      (e.inv ≫ laxPullbackSnd P Q ≫ equivalencePathReplacementProjection b ≫ b) := by
    simpa only [FunctorIso, Category.assoc] using
      FunctorIso.precomp (equivalencePathReplacementFunctorIso b).symm (e.inv ≫ laxPullbackSnd P Q)
  have h₃ : FunctorIso
      (e.inv ≫ laxPullbackSnd P Q ≫ equivalencePathReplacementProjection b ≫ b)
      (laxPullbackSnd p q ≫ b) := by
    simpa only [FunctorIso, Category.assoc, reassoc_of% hπ, Category.id_comp] using
      e.invHomIso.postcomp (laxPullbackSnd p q ≫ b)
  have heq : (laxPullbackCospanIsoEquivalence p q p' q' a b c hp hq ha hb hc).hom ≫
      laxPullbackSnd p' q' = e.inv ≫ laxPullbackSnd P Q ≫ equivalencePathReplacementMap b := by
    change (e.inv ≫ cospanPathLaxTarget p q p' q' a b c hp hq) ≫ _ = _
    rw [Category.assoc, hγ]
  exact functorIsoOfEq (h₂.trans h₃) heq.symm rfl

end SerrePositivity.InfinityCategories.F2
