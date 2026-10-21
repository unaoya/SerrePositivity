module

public import SerrePositivity.KST.LocalizingInvariants.LaxCounitQuotientDiagram
public import SerrePositivity.KST.LocalizingInvariants.CofiberRelativeRightComparison
public import SerrePositivity.KST.LocalizingInvariants.FunctorHomArrowTransport

/-!
概要：商へ写した元の cofiber と選択した cofiber の比較は、右辺とその始点を保つ。
方針：同じ底辺の全図式比較の自然性と始点の恒等式を、そのまま適用する。
規約：商や cofiber 右辺を選び直さない。使われ方：元の fiber との二次の比較。
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

def quotientRightSourceComparison :=
  homPost (CofiberDiagrams.right Q.obj ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (quotientDiagramComparison p q i r).hom

def quotientRightTargetComparison :=
  homPost (CofiberDiagrams.right Q.obj ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (quotientDiagramComparison p q i r).hom

lemma quotientRightComparison_naturality :
    quotientRightSourceComparison p q i r ≫ arrowFamilyHom
      (CofiberDiagrams.lift Q.obj (quotientArrow p q i r) ≫ CofiberDiagrams.right Q.obj) =
        arrowFamilyHom (quotientOriginalDiagrams p q i r ≫ CofiberDiagrams.right Q.obj) ≫
          quotientRightTargetComparison p q i r :=
  CofiberDiagrams.relativeComparison_right_naturality Q.obj _ _
    (quotientOriginalDiagrams_sameBottom p q i r)

lemma quotientRightSourceComparison_arrow :
    Arrow.mk (quotientRightSourceComparison p q i r) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex
        (CofiberDiagrams.lift Q.obj (quotientArrow p q i r) ≫ (CofiberDiagrams.right Q.obj ≫
          evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))) :
            hoFunctor.obj ((ihom A.obj).obj Q.obj))) :=
  CofiberDiagrams.relativeComparison_rightSource_arrow Q.obj _ _
    (quotientOriginalDiagrams_sameBottom p q i r)

lemma quotientOriginalDiagrams_right :
    quotientOriginalDiagrams p q i r ≫ CofiberDiagrams.right Q.obj =
      (i.hom ≫ CofiberFamily.rightArrow (laxCategory p q).obj (arrow p q)) ≫
        (ihom (Δ[1] : SSet.{u})).map r.hom := by
  rw [quotientOriginalDiagrams, Category.assoc, CofiberDiagrams.postcomp_right]
  change (i.hom ≫ CofiberDiagrams.lift (laxCategory p q).obj (arrow p q)) ≫
    ((CofiberDiagrams.inclusion (laxCategory p q).obj ≫ (pre squareRightEdge).app _) ≫ _) = _
  rw [← Category.assoc, ← Category.assoc,
    Category.assoc i.hom, CofiberDiagrams.lift_inclusion]
  rfl

lemma quotientOriginalDiagrams_cofiber :
    quotientOriginalDiagrams p q i r ≫ (CofiberDiagrams.right Q.obj ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) =
        (i.hom ≫ cofiber p q) ≫ r.hom := by
  rw [quotientOriginalDiagrams, Category.assoc, CofiberDiagrams.postcomp_cofiber,
    ← Category.assoc, ← Category.assoc]
  have he := CofiberDiagrams.lift_right_target (laxCategory p q).obj (arrow p q)
  calc
    _ = (i.hom ≫ ((CofiberDiagrams.lift (laxCategory p q).obj (arrow p q) ≫
        CofiberDiagrams.right (laxCategory p q).obj) ≫
          evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) ≫ r.hom := by
      simp only [Category.assoc]
    _ = _ := by rw [he]; rfl

lemma quotientSelectedDiagrams_cofiber :
    CofiberDiagrams.lift Q.obj (quotientArrow p q i r) ≫ (CofiberDiagrams.right Q.obj ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) =
        CofiberFamily.cofiber Q.obj (quotientArrow p q i r) := by
  rw [← Category.assoc, CofiberDiagrams.lift_right_target]

def quotientCofiberRelativeIso : FunctorIso ((i.hom ≫ cofiber p q) ≫ r.hom)
    (CofiberFamily.cofiber Q.obj (quotientArrow p q i r)) :=
  (eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f))
    (quotientOriginalDiagrams_cofiber p q i r))).symm ≪≫
  FunctorIso.postcomp (quotientDiagramComparison p q i r)
    (CofiberDiagrams.right Q.obj ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≪≫
  eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f))
    (quotientSelectedDiagrams_cofiber p q i r))

lemma quotientCofiberRelativeIso_arrow :
    Arrow.mk (quotientCofiberRelativeIso p q i r).hom =
      Arrow.mk (quotientRightTargetComparison p q i r) := by
  unfold quotientCofiberRelativeIso
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv]
  rw [← Category.assoc, arrow_mk_comp_eqToHom, arrow_mk_eqToHom_comp,
    HomotopyLimits.functorIso_postcomp_hom]
  rfl

end SerrePositivity.KST.LocalizingInvariants.LaxCounit
