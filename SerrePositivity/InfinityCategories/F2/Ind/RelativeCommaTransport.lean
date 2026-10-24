module

public import SerrePositivity.InfinityCategories.F2.Ind.RelativeCommaComparison
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationEquivalenceLifting
public import
  SerrePositivity.InfinityCategories.F1.FunctorCategories.PathCorrectedSquarePrecompositionCoherence
public import SerrePositivity.InfinityCategories.F1.Pullbacks.PullbackCommonNormalizedIso
/-!
概要：元の任意の関手同型に沿って指定下側変換を移し、実 under comma の比較を得る。
方針：left fibration 上の指定 path を厳密化し、その同じ同型を二成分の比較へ束ねる。
規約：元の関手同型と指定変換を保持し、pullback の Kan 性を仮定しない。
使われ方：終点評価の下での元の補間旧族と試験族の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：指定下側変換を元の上側同型に沿って輸送すると、同じ実 under comma で同型。
方針：同じ指定 path の像の一致で貼り合わせる。
規約：元の比較と指定値を保持。使われ方：終点評価下の相対余錐の帰還。 -/
lemma exists_relativeCommaFamily_iso_of_functorIso
    {A K E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    (e : E ⟶ B) (z : K ⟶ B) (f g : A ⟶ E) (t : A ⟶ sliceUnder z)
    (ht : g ≫ e = t ≫ sliceUnderProjection z) (d : FunctorIso f g) :
    ∃ (t' : A ⟶ sliceUnder z) (hf : f ≫ e = t' ≫ sliceUnderProjection z),
      Nonempty (FunctorIso (relativeCommaFamily e z t' f hf)
        (relativeCommaFamily e z t g ht)) := by
  let p := sliceUnderProjection z
  let d' := F2.functorIsoOfEq (d.postcomp e) rfl ht
  let c := pathCorrectedFunctorSquare p (leftFibration_equivalenceLifting p) t (f ≫ e) d'
  let a := relativeCommaFamily e z c.map f c.comm.symm
  let b := relativeCommaFamily e z t g ht
  have ha₀ : a ≫ pullback.fst p e = c.map := pullback.lift_fst _ _ _
  have hb₀ : b ≫ pullback.fst p e = t := pullback.lift_fst _ _ _
  have ha₁ : a ≫ pullback.snd p e = f := pullback.lift_snd _ _ _
  have hb₁ : b ≫ pullback.snd p e = g := pullback.lift_snd _ _ _
  let L := F2.functorIsoOfEq c.exactComponentIso ha₀.symm hb₀.symm
  let R := F2.functorIsoOfEq d ha₁.symm hb₁.symm
  have hL₀ : (a ≫ pullback.fst p e) ≫ p = f ≫ e :=
    (congrArg (fun v => v ≫ p) ha₀).trans c.comm
  have hL₁ : (b ≫ pullback.fst p e) ≫ p = g ≫ e :=
    (congrArg (fun v => v ≫ p) hb₀).trans ht.symm
  have hR₀ : (a ≫ pullback.snd p e) ≫ e = f ≫ e := congrArg (fun v => v ≫ e) ha₁
  have hR₁ : (b ≫ pullback.snd p e) ≫ e = g ≫ e := congrArg (fun v => v ≫ e) hb₁
  have hc : HEq (c.exactComponentIso.postcomp p) d' :=
    (F2.functorIsoOfEq_heq _ c.comm rfl).symm.trans
      (heq_of_eq c.exactComponentIso_postcomp_normalized)
  have hl : HEq (F2.functorIsoOfEq (L.postcomp p) hL₀ hL₁) (d.postcomp e) :=
    (F2.functorIsoOfEq_heq _ _ _).trans
      ((functorIsoOfEq_postcomp_heq _ _ _ _).trans
        (hc.trans (F2.functorIsoOfEq_heq _ _ _)))
  have hr : HEq (F2.functorIsoOfEq (R.postcomp e) hR₀ hR₁) (d.postcomp e) :=
    (F2.functorIsoOfEq_heq _ _ _).trans (functorIsoOfEq_postcomp_heq _ _ _ _)
  exact ⟨c.map, c.comm.symm, ⟨pullbackFunctorIsoOfCommonNormalizedIsos p e a b L R
    hL₀ hL₁ hR₀ hR₁ (eq_of_heq (hl.trans hr.symm))⟩⟩
end SerrePositivity.InfinityCategories.F2.Ind
