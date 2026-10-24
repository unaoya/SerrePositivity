module

public import SerrePositivity.InfinityCategories.F1.Pullbacks.PullbackCompatibleFunctorIso
public import SerrePositivity.InfinityCategories.F2.Ind.FullyFaithfulSquareRelativeIsoReflection
/-!
概要：指定した下側変換を保つ二つの comma 族の比較を、実 under comma 内へ戻す。
方針：下側の恒等同型と上側の指定同型を、left fibration の引き戻しで束ねる。
規約：元の二族と指定変換を保持し、pullback の Kan 性を仮定しない。
使われ方：Ind 射図式の始点評価下の相対補間と余錐の帰還。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {A K E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
  (e : E ⟶ B) (z : K ⟶ B) (f g : A ⟶ E) (t : A ⟶ sliceUnder z)
  (hf : f ≫ e = t ≫ sliceUnderProjection z) (hg : g ≫ e = t ≫ sliceUnderProjection z)
/-- 概要：指定した下側変換と元の全族を、実 under comma の族へ束ねる。
方針：厳密な pullback の普遍性を使う。規約：同じ全射を保持。
使われ方：相対補間の元のパラメーター族。 -/
def relativeCommaFamily (f : A ⟶ E) (h : f ≫ e = t ≫ sliceUnderProjection z) :=
  pullback.lift t f h.symm
/-- 概要：同じ下側変換の下で、射影が元の等号同型となる指定比較を実 comma 内へ戻す。
方針：二成分を貼り合わせ、左ファイブレーションで可逆性を反映する。
規約：同じ全族と指定変換を保持。使われ方：補間余錐の元の試験族への帰還。 -/
lemma nonempty_relativeCommaFamily_iso (d : FunctorIso f g)
    (hd : d.postcomp e = eqToIso (congrArg
      (fun v => SSet.HomotopyCategory.mk (functorVertex v)) (hf.trans hg.symm))) :
    Nonempty (FunctorIso (relativeCommaFamily e z t f hf)
      (relativeCommaFamily e z t g hg)) := by
  let p := sliceUnderProjection z
  let a := relativeCommaFamily e z t f hf
  let b := relativeCommaFamily e z t g hg
  have ha₀ : a ≫ pullback.fst p e = t := pullback.lift_fst _ _ _
  have hb₀ : b ≫ pullback.fst p e = t := pullback.lift_fst _ _ _
  have ha₁ : a ≫ pullback.snd p e = f := pullback.lift_snd _ _ _
  have hb₁ : b ≫ pullback.snd p e = g := pullback.lift_snd _ _ _
  let L := F2.functorIsoOfEq (show FunctorIso t t from Iso.refl _) ha₀.symm hb₀.symm
  let R := F2.functorIsoOfEq d ha₁.symm hb₁.symm
  have hL : F2.IsFunctorEqIso L :=
    (show F2.IsFunctorEqIso (show FunctorIso t t from Iso.refl _) from ⟨rfl, rfl⟩).of_heq
      ha₀.symm hb₀.symm (F2.functorIsoOfEq_heq _ _ _)
  have hLp : F2.IsFunctorEqIso (F2.functorIsoOfEq (L.postcomp p)
      (pullbackProjectionComposite_eq p e a) (pullbackProjectionComposite_eq p e b)) :=
    (hL.postcomp p).of_heq (pullbackProjectionComposite_eq p e a)
      (pullbackProjectionComposite_eq p e b) (F2.functorIsoOfEq_heq _ _ _)
  have hR : F2.IsFunctorEqIso (R.postcomp e) := by
    have hde : F2.IsFunctorEqIso (d.postcomp e) := by
      rw [hd]
      exact isFunctorEqIso_eqToIso (hf.trans hg.symm)
    exact hde.of_heq (congrArg (fun v => v ≫ e) ha₁.symm)
      (congrArg (fun v => v ≫ e) hb₁.symm) (functorIsoOfEq_postcomp_heq _ _ _ _)
  have hbase : (a ≫ pullback.snd p e) ≫ e = (b ≫ pullback.snd p e) ≫ e := by
    rw [ha₁, hb₁]
    exact hf.trans hg.symm
  exact ⟨pullbackFunctorIsoOfCompatibleIsos p e a b L R
    ((hLp.eq hbase).trans (hR.eq hbase).symm)⟩
end SerrePositivity.InfinityCategories.F2.Ind
