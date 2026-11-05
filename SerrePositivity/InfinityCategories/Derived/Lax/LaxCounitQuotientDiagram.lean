module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams
public import SerrePositivity.KST.LocalizingInvariants.CofiberRelativeDiagramComparison
public import SerrePositivity.InfinityCategories.Derived.Lax.LaxCounitQuotientComparison
public import SerrePositivity.KST.LocalizingInvariants.LaxCounitUnitComparison

/-!
概要：包含で制限し商へ写した元の余単位 cofiber を、同じ底辺の全図式で比較する。
方針：元の図式全族を完全関手で写し、底辺評価の同じ fiber 内で比較する。
規約：底辺に射影した比較は恒等。使われ方：指定右辺を保つ商の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxCounit
end SerrePositivity.KST.LocalizingInvariants.LaxCounit
namespace SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit
open SerrePositivity.KST.LocalizingInvariants.LaxCounit
variable {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)

def quotientOriginalDiagrams : A.obj ⟶ CofiberDiagrams.space Q.obj :=
  (i.hom ≫ CofiberDiagrams.lift (laxCategory p q).obj (arrow p q)) ≫
    CofiberDiagrams.postcomp r.hom

lemma quotientOriginalDiagrams_bottom :
    quotientOriginalDiagrams p q i r ≫ CofiberDiagrams.bottom Q.obj =
      quotientArrow p q i r := by
  rw [quotientOriginalDiagrams, Category.assoc, CofiberDiagrams.postcomp_bottom,
    ← Category.assoc, Category.assoc i.hom, CofiberDiagrams.lift_bottom]
  rfl

lemma quotientOriginalDiagrams_squares :
    quotientOriginalDiagrams p q i r ≫ CofiberDiagrams.inclusion Q.obj =
      (i.hom ≫ CofiberFamily.squares (laxCategory p q).obj (arrow p q)) ≫
        (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map r.hom := by
  rw [quotientOriginalDiagrams, Category.assoc, CofiberDiagrams.postcomp_inclusion,
    ← Category.assoc, Category.assoc i.hom, CofiberDiagrams.lift_inclusion]

lemma quotientOriginalDiagrams_sameBottom :
    quotientOriginalDiagrams p q i r ≫ CofiberDiagrams.bottom Q.obj =
      CofiberDiagrams.lift Q.obj (quotientArrow p q i r) ≫ CofiberDiagrams.bottom Q.obj := by
  rw [quotientOriginalDiagrams_bottom, CofiberDiagrams.lift_bottom]

def quotientDiagramComparison : FunctorIso (quotientOriginalDiagrams p q i r)
    (CofiberDiagrams.lift Q.obj (quotientArrow p q i r)) :=
  CofiberDiagrams.relativeComparison Q.obj _ _ (quotientOriginalDiagrams_sameBottom p q i r)

lemma quotientDiagramComparison_bottom_arrow :
    Arrow.mk (FunctorIso.postcomp (quotientDiagramComparison p q i r)
      (CofiberDiagrams.bottom Q.obj)).hom =
        Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex
          (CofiberDiagrams.lift Q.obj (quotientArrow p q i r) ≫ CofiberDiagrams.bottom Q.obj)) :
            hoFunctor.obj ((ihom A.obj).obj ((ihom (Δ[1] : SSet.{u})).obj Q.obj)))) :=
  CofiberDiagrams.relativeComparison_bottom_arrow Q.obj _ _
    (quotientOriginalDiagrams_sameBottom p q i r)

def quotientSquareComparison : FunctorIso
    (quotientOriginalDiagrams p q i r ≫ CofiberDiagrams.inclusion Q.obj)
    (CofiberFamily.squares Q.obj (quotientArrow p q i r)) := by
  have e := FunctorIso.postcomp (quotientDiagramComparison p q i r)
    (CofiberDiagrams.inclusion Q.obj)
  rw [CofiberDiagrams.lift_inclusion] at e
  exact e

end SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientDiagramComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientDiagramComparison := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientDiagramComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientDiagramComparison_bottom_arrow := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientDiagramComparison_bottom_arrow

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalDiagrams (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientOriginalDiagrams := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalDiagrams

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientOriginalDiagrams_bottom := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalDiagrams_bottom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientOriginalDiagrams_sameBottom := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalDiagrams_sameBottom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientOriginalDiagrams_squares := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalDiagrams_squares

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSquareComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientSquareComparison := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSquareComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientOriginalDiagrams._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalDiagrams._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientOriginalDiagrams._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalDiagrams._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientOriginalDiagrams._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalDiagrams._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientOriginalDiagrams.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientOriginalDiagrams.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit.quotientSquareComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxCounit.quotientSquareComparison._proof_1
