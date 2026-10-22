module

public import SerrePositivity.KST.NonConnective.DGKappaSuspension
public import SerrePositivity.KST.NonConnective.DGSwindleStrict

/-!
概要：同じ明示入力の κ-compact dg cone 上で、構成済みの実 swindle を保持する。
方針：実 dg 直和関手と両向きの厳密自然変換を、同じ充満部分圏へ制限する。
規約：swindle の存在は入力に含めず、成分は元の指定した閉 dg 同型。
使われ方：連結 K の加法性に渡す id ⊕ T ≅ T の dg 側。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories DGNerve
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 同じ κ-compact dg cone 上の id ⊕ T。 -/
def dgKappaSwindleSource : DGFunctor R (DGKappaCone R D I) (DGKappaCone R D I) :=
  (dgSwindleSourceFunctor R D).restrict I.objects I.objects (by
    intro M hM
    exact I.binaryClosed M (dgCountableSumObj R D M) hM
      (I.countableClosed (fun _ : ℕ ↦ M) (fun _ ↦ hM)))

/-- 全斉次射の自然性を保った、同じ cone 内の順向き swindle。 -/
def dgKappaSwindleStrictHom :
    StrictNatTrans (dgKappaSwindleSource R D I) (dgKappaConeCountableSum R D I) where
  app X := (dgSwindleStrictHom R D).app X.val
  naturality f := (dgSwindleStrictHom R D).naturality f

/-- 全斉次射の自然性を保った、同じ cone 内の逆向き swindle。 -/
def dgKappaSwindleStrictInv :
    StrictNatTrans (dgKappaConeCountableSum R D I) (dgKappaSwindleSource R D I) where
  app X := (dgSwindleStrictInv R D).app X.val
  naturality f := (dgSwindleStrictInv R D).naturality f

/-- 同じ cone 内での各成分の実閉 dg 同型。両側逆は既に証明した指定射。 -/
def dgKappaSwindleComponentIso (X : DGKappaCone R D I) :
    ForgetEnrichment.of (Complex R) ((dgKappaSwindleSource R D I).obj X) ≅
      ForgetEnrichment.of (Complex R) ((dgKappaConeCountableSum R D I).obj X) where
  hom := (countableSwindleIso (ModuleCategory R D) X.val).hom
  inv := (countableSwindleIso (ModuleCategory R D) X.val).inv
  hom_inv_id := (countableSwindleIso (ModuleCategory R D) X.val).hom_inv_id
  inv_hom_id := (countableSwindleIso (ModuleCategory R D) X.val).inv_hom_id

/-- 順向きの厳密 dg 自然変換の成分は、同じ実閉同型の cycle。 -/
lemma dgKappaSwindleStrictHom_app (X : DGKappaCone R D I) :
    (dgKappaSwindleStrictHom R D I).app X =
      cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (dgKappaSwindleComponentIso R D I X).hom) :=
  rfl

/-- 逆向きの厳密 dg 自然変換の成分も、同じ実閉同型の逆の cycle。 -/
lemma dgKappaSwindleStrictInv_app (X : DGKappaCone R D I) :
    (dgKappaSwindleStrictInv R D I).app X =
      cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (dgKappaSwindleComponentIso R D I X).inv) :=
  rfl

end SerrePositivity.KST.NonConnective
