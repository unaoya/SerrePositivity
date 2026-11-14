module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactFunctor
public import SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.ExactArrowMap
public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyPrecomposition
public import SerrePositivity.KST.LocalizingInvariants.CofiberZeroTargetComparison
public import SerrePositivity.KST.LocalizingInvariants.LaxCounitCComparison
public import SerrePositivity.KST.LocalizingInvariants.LaxInclusions
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientShiftLegs

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax
open _root_.SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit
variable {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i r)

def quotientArrow : A.obj ⟶ (ihom (Δ[1] : SSet.{u})).obj Q.obj :=
  (i.hom ≫ arrow p q) ≫ (ihom (Δ[1] : SSet.{u})).map r.hom

lemma quotientArrow_source : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      (i.hom ≫ (laxSnd p q).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg p q r).hom := by
  change ((i.hom ≫ arrow p q) ≫ (ihom (Δ[1] : SSet.{u})).map r.hom) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      (i.hom ≫ (laxSnd p q).hom) ≫ (LaxInclusion.fromD p q ≫ r.hom)
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.arrowMap_evaluation, ← Category.assoc,
    Category.assoc i.hom (arrow p q), arrow_source]
  simp only [Category.assoc]

lemma quotientArrow_target : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = i.hom ≫ r.hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.arrowMap_evaluation, ← Category.assoc,
    Category.assoc i.hom (arrow p q), arrow_target, Category.comp_id]

include h in
lemma quotientArrow_zero_target (x : A.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r).app (Opposite.op ⦋0⦌) x) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _).app _ x)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow_target]
  exact h.kills_inclusion x

def quotientCofiberComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((i.hom ≫ cofiber p q) ≫ r.hom) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber Q.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (CofiberFamily.precompositionIso (arrow p q) i.hom) r.hom ≪≫
    CofiberFamily.familyExactComparison r.hom (i.hom ≫ arrow p q)

def quotientCofiber_CIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber Q.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r))
    ((i.hom ≫ (laxFst p q).hom) ≫ (LaxInclusion.fromC p q ≫ r.hom)) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (cofiber_fromCIso p q) i.hom) r.hom
  have he := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiberComparison p q i r).symm ≪≫ e
  simpa only [Category.assoc] using he

def quotientCofiber_DSuspIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber Q.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r))
    (((i.hom ≫ (laxSnd p q).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg p q r).hom) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.map Q.obj) := by
  have e := cofiberZeroTargetIso Q.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow_zero_target p q i r h)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow_source] at e
  exact e

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientArrow := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientArrow_source := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientArrow_target := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow_target

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientArrow_zero_target := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow_zero_target

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiberComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCofiberComparison := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiberComparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiber_CIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCofiber_CIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiber_CIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiber_DSuspIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCofiber_DSuspIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiber_DSuspIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientArrow.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCofiberComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiberComparison._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCofiberComparison._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiberComparison._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCofiberComparison._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiberComparison._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCofiber_CIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiber_CIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCofiber_CIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiber_CIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCofiber_DSuspIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiber_DSuspIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientCofiber_DSuspIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiber_DSuspIso._proof_2
