module

public import SerrePositivity.InfinityCategories.F2.Ind.RelativeCommaTransport

/-!
概要：同じ上側全族を保ち、底の像が等号同型である下側比較を実 under comma へ戻す。
方針：指定下側同型と上側恒等同型を、同じ実 pullback で貼り合わせる。
規約：元の上側族と指定変換の値を保持する。
使われ方：全余錐から戻した指定下側変換の旧族上の相殺。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：元の同じ上側族で、底固定の下側比較は実 under comma の比較になる。
方針：二成分の指定像を等号同型で照合。
規約：同じ全族と指定値。使われ方：元の指定変換の下の余錐への帰還。 -/
lemma nonempty_relativeCommaFamily_iso_of_lowerIso
    {A K E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    (e : E ⟶ B) (z : K ⟶ B) (q : A ⟶ E) (t t' : A ⟶ sliceUnder z)
    (ht : q ≫ e = t ≫ sliceUnderProjection z)
    (ht' : q ≫ e = t' ≫ sliceUnderProjection z)
    (d : FunctorIso t t') (hd : F2.IsFunctorEqIso (d.postcomp (sliceUnderProjection z))) :
    Nonempty (FunctorIso (relativeCommaFamily e z t q ht)
      (relativeCommaFamily e z t' q ht')) := by
  let p := sliceUnderProjection z
  let a := relativeCommaFamily e z t q ht
  let b := relativeCommaFamily e z t' q ht'
  have ha₀ : a ≫ pullback.fst p e = t := pullback.lift_fst _ _ _
  have hb₀ : b ≫ pullback.fst p e = t' := pullback.lift_fst _ _ _
  have ha₁ : a ≫ pullback.snd p e = q := pullback.lift_snd _ _ _
  have hb₁ : b ≫ pullback.snd p e = q := pullback.lift_snd _ _ _
  let L := F2.functorIsoOfEq d ha₀.symm hb₀.symm
  let R := F2.functorIsoOfEq (show FunctorIso q q from Iso.refl _) ha₁.symm hb₁.symm
  have hLp : F2.IsFunctorEqIso (F2.functorIsoOfEq (L.postcomp p)
      (pullbackProjectionComposite_eq p e a) (pullbackProjectionComposite_eq p e b)) :=
    (hd.of_heq (congrArg (fun m ↦ m ≫ p) ha₀.symm)
      (congrArg (fun m ↦ m ≫ p) hb₀.symm)
      (functorIsoOfEq_postcomp_heq _ _ _ _)).of_heq
      (pullbackProjectionComposite_eq p e a) (pullbackProjectionComposite_eq p e b)
      (F2.functorIsoOfEq_heq _ _ _)
  have hR : F2.IsFunctorEqIso (R.postcomp e) :=
    ((show F2.IsFunctorEqIso (show FunctorIso q q from Iso.refl _) from ⟨rfl, rfl⟩).of_heq
      ha₁.symm hb₁.symm (F2.functorIsoOfEq_heq _ _ _)).postcomp e
  have hbase : (a ≫ pullback.snd p e) ≫ e = (b ≫ pullback.snd p e) ≫ e := by
    rw [ha₁, hb₁]
  exact ⟨pullbackFunctorIsoOfCompatibleIsos p e a b L R
    ((hLp.eq hbase).trans (hR.eq hbase).symm)⟩
end SerrePositivity.InfinityCategories.F2.Ind
