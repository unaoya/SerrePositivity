module

public import SerrePositivity.KST.LocalizingInvariants.LaxCounitCComparison
public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyPrecomposition
public import SerrePositivity.KST.LocalizingInvariants.CofiberZeroTargetComparison
public import SerrePositivity.KST.LocalizingInvariants.LaxQuotientShiftLegs

/-!
概要：D 随伴余単位を Verdier 包含へ制限して商へ写すと、零終点の実 cofiber 族になる。
方針：元の cofiber の制限と完全後合成の比較を、C 包含と逆 shift の二脚に接続する。
規約：核の一致だけを使う部分も元の商 r を保持。使われ方：二脚の全関手比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxCounit
variable {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)
  (h : IsVerdierSequence i r)

def quotientArrow : A.obj ⟶ (ihom (Δ[1] : SSet.{u})).obj Q.obj :=
  (i.hom ≫ arrow p q) ≫ (ihom (Δ[1] : SSet.{u})).map r.hom

lemma quotientArrow_source : quotientArrow p q i r ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      (i.hom ≫ (laxSnd p q).hom) ≫ (laxQuotientDLeg p q r).hom := by
  change ((i.hom ≫ arrow p q) ≫ (ihom (Δ[1] : SSet.{u})).map r.hom) ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      (i.hom ≫ (laxSnd p q).hom) ≫ (LaxInclusion.fromD p q ≫ r.hom)
  rw [Category.assoc, arrowMap_evaluation, ← Category.assoc,
    Category.assoc i.hom (arrow p q), arrow_source]
  simp only [Category.assoc]

lemma quotientArrow_target : quotientArrow p q i r ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = i.hom ≫ r.hom := by
  rw [quotientArrow, Category.assoc, arrowMap_evaluation, ← Category.assoc,
    Category.assoc i.hom (arrow p q), arrow_target, Category.comp_id]

include h in
lemma quotientArrow_zero_target (x : A.obj _⦋0⦌) :
    IsZeroTargetArrow ((quotientArrow p q i r).app (Opposite.op ⦋0⦌) x) := by
  change IsZeroVertex ((quotientArrow p q i r ≫ evaluateFunctorAt _).app _ x)
  rw [quotientArrow_target]
  exact h.kills_inclusion x

def quotientCofiberComparison : FunctorIso
    ((i.hom ≫ cofiber p q) ≫ r.hom) (CofiberFamily.cofiber Q.obj (quotientArrow p q i r)) :=
  FunctorIso.postcomp (CofiberFamily.precompositionIso (arrow p q) i.hom) r.hom ≪≫
    CofiberFamily.familyExactComparison r.hom (i.hom ≫ arrow p q)

def quotientCofiber_CIso : FunctorIso (CofiberFamily.cofiber Q.obj (quotientArrow p q i r))
    ((i.hom ≫ (laxFst p q).hom) ≫ (LaxInclusion.fromC p q ≫ r.hom)) := by
  have e := FunctorIso.postcomp (FunctorIso.precomp (cofiber_fromCIso p q) i.hom) r.hom
  have he := (quotientCofiberComparison p q i r).symm ≪≫ e
  simpa only [Category.assoc] using he

def quotientCofiber_DSuspIso : FunctorIso (CofiberFamily.cofiber Q.obj (quotientArrow p q i r))
    (((i.hom ≫ (laxSnd p q).hom) ≫ (laxQuotientDLeg p q r).hom) ≫
      SuspensionExact.map Q.obj) := by
  have e := cofiberZeroTargetIso Q.obj (quotientArrow p q i r)
    (quotientArrow_zero_target p q i r h)
  rw [quotientArrow_source] at e
  exact e

end SerrePositivity.KST.LocalizingInvariants.LaxCounit
