module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Exact.SuspensionExactFunctor
public import SerrePositivity.InfinityCategories.StablePresentable.Exact.ExactArrowMap
public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyPrecomposition
public import SerrePositivity.KST.LocalizingInvariants.CofiberZeroTargetComparison
public import SerrePositivity.KST.LocalizingInvariants.LaxCounitCComparison
public import SerrePositivity.KST.LocalizingInvariants.LaxInclusions
public import SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientShiftLegs

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxCounit
end SerrePositivity.KST.LocalizingInvariants.LaxCounit
namespace SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.LocalizingInvariants.LaxCounit
variable {C D E A Q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i r)

def quotientArrow : A.obj ⟶ (ihom (Δ[1] : SSet.{u})).obj Q.obj :=
  (i.hom ≫ arrow p q) ≫ (ihom (Δ[1] : SSet.{u})).map r.hom

lemma quotientArrow_source : _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow p q i r ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      (i.hom ≫ (laxSnd p q).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientDLeg p q r).hom := by
  change ((i.hom ≫ arrow p q) ≫ (ihom (Δ[1] : SSet.{u})).map r.hom) ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      (i.hom ≫ (laxSnd p q).hom) ≫ (LaxInclusion.fromD p q ≫ r.hom)
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.StablePresentable.Exact.arrowMap_evaluation, ← Category.assoc,
    Category.assoc i.hom (arrow p q), arrow_source]
  simp only [Category.assoc]

lemma quotientArrow_target : _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow p q i r ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = i.hom ≫ r.hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow, Category.assoc, _root_.SerrePositivity.InfinityCategories.StablePresentable.Exact.arrowMap_evaluation, ← Category.assoc,
    Category.assoc i.hom (arrow p q), arrow_target, Category.comp_id]

include h in
lemma quotientArrow_zero_target (x : A.obj _⦋0⦌) :
    IsZeroTargetArrow ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow p q i r).app (Opposite.op ⦋0⦌) x) := by
  change IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow p q i r ≫ evaluateFunctorAt _).app _ x)
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow_target]
  exact h.kills_inclusion x

def quotientCofiberComparison : FunctorIso
    ((i.hom ≫ cofiber p q) ≫ r.hom) (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber Q.obj (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow p q i r)) :=
  FunctorIso.postcomp (CofiberFamily.precompositionIso (arrow p q) i.hom) r.hom ≪≫
    CofiberFamily.familyExactComparison r.hom (i.hom ≫ arrow p q)

def quotientCofiber_CIso : FunctorIso (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber Q.obj (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow p q i r))
    ((i.hom ≫ (laxFst p q).hom) ≫ (LaxInclusion.fromC p q ≫ r.hom)) := by
  have e := FunctorIso.postcomp (FunctorIso.precomp (cofiber_fromCIso p q) i.hom) r.hom
  have he := (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiberComparison p q i r).symm ≪≫ e
  simpa only [Category.assoc] using he

def quotientCofiber_DSuspIso : FunctorIso (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber Q.obj (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow p q i r))
    (((i.hom ≫ (laxSnd p q).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientDLeg p q r).hom) ≫
      _root_.SerrePositivity.InfinityCategories.Stable.Exact.SuspensionExact.map Q.obj) := by
  have e := cofiberZeroTargetIso Q.obj (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow p q i r)
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow_zero_target p q i r h)
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow_source] at e
  exact e

end SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientArrow := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientArrow_source := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientArrow_target := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow_target

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientArrow_zero_target := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow_zero_target

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiberComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCofiberComparison := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiberComparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiber_CIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCofiber_CIso := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiber_CIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiber_DSuspIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCofiber_DSuspIso := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiber_DSuspIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientArrow.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientArrow.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCofiberComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiberComparison._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCofiberComparison._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiberComparison._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCofiberComparison._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiberComparison._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCofiber_CIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiber_CIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCofiber_CIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiber_CIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCofiber_DSuspIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiber_DSuspIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCofiber_DSuspIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientCofiber_DSuspIso._proof_2
