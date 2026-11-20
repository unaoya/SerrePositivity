module


public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams
public import SerrePositivity.KST.LocalizingInvariants.CofiberRelativeDiagramComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxCounitQuotientComparison
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax
open _root_.SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit
variable {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)

def quotientOriginalDiagrams : A.obj ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.space Q.obj :=
  (i.hom ≫ CofiberDiagrams.lift (laxCategory p q).obj (arrow p q)) ≫
    _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.postcomp r.hom

lemma quotientOriginalDiagrams_bottom :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalDiagrams p q i r ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom Q.obj =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalDiagrams, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.postcomp_bottom,
    ← Category.assoc, Category.assoc i.hom, CofiberDiagrams.lift_bottom]
  rfl

lemma quotientOriginalDiagrams_squares :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalDiagrams p q i r ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.inclusion Q.obj =
      (i.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.squares (laxCategory p q).obj (arrow p q)) ≫
        (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map r.hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalDiagrams, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.postcomp_inclusion,
    ← Category.assoc, Category.assoc i.hom, CofiberDiagrams.lift_inclusion]

lemma quotientOriginalDiagrams_sameBottom :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalDiagrams p q i r ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom Q.obj =
      CofiberDiagrams.lift Q.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom Q.obj := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalDiagrams_bottom, CofiberDiagrams.lift_bottom]

def quotientDiagramComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalDiagrams p q i r)
    (CofiberDiagrams.lift Q.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r)) :=
  CofiberDiagrams.relativeComparison Q.obj _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalDiagrams_sameBottom p q i r)

lemma quotientDiagramComparison_bottom_arrow :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientDiagramComparison p q i r)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom Q.obj)).hom =
        Arrow.mk (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
          (CofiberDiagrams.lift Q.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom Q.obj)) :
            hoFunctor.obj ((ihom A.obj).obj ((ihom (Δ[1] : SSet.{u})).obj Q.obj)))) :=
  CofiberDiagrams.relativeComparison_bottom_arrow Q.obj _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalDiagrams_sameBottom p q i r)

def quotientSquareComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalDiagrams p q i r ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.inclusion Q.obj)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.squares Q.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r)) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientDiagramComparison p q i r)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.inclusion Q.obj)
  rw [CofiberDiagrams.lift_inclusion] at e
  exact e

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
