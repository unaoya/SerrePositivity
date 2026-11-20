module


public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberFamilyRightHom
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.ArrowFamilyHomNaturality
public import SerrePositivity.KST.LocalizingInvariants.CofiberRelativeRightComparison
public import SerrePositivity.KST.LocalizingInvariants.CofiberRotationExact
public import SerrePositivity.KST.LocalizingInvariants.FunctorHomArrowTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxCounitQuotientDiagram

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxCounit
end SerrePositivity.KST.LocalizingInvariants.LaxCounit
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax
open _root_.SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.KST.LocalizingInvariants.LaxCounit
variable {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)

def quotientRightSourceComparison :=
  homPost (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right Q.obj ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientDiagramComparison p q i r).hom

def quotientRightTargetComparison :=
  homPost (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right Q.obj ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientDiagramComparison p q i r).hom

lemma quotientRightComparison_naturality :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientRightSourceComparison p q i r ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.arrowFamilyHom
      (CofiberDiagrams.lift Q.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right Q.obj) =
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.arrowFamilyHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalDiagrams p q i r ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right Q.obj) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientRightTargetComparison p q i r :=
  CofiberDiagrams.relativeComparison_right_naturality Q.obj _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalDiagrams_sameBottom p q i r)

lemma quotientRightSourceComparison_arrow :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientRightSourceComparison p q i r) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
        (CofiberDiagrams.lift Q.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r) ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right Q.obj ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))) :
            hoFunctor.obj ((ihom A.obj).obj Q.obj))) :=
  CofiberDiagrams.relativeComparison_rightSource_arrow Q.obj _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalDiagrams_sameBottom p q i r)

lemma quotientOriginalDiagrams_right :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalDiagrams p q i r ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right Q.obj =
      (i.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.rightArrow (laxCategory p q).obj (arrow p q)) ≫
        (ihom (Δ[1] : SSet.{u})).map r.hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalDiagrams, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.postcomp_right]
  change (i.hom ≫ CofiberDiagrams.lift (laxCategory p q).obj (arrow p q)) ≫
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.inclusion (laxCategory p q).obj ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge).app _) ≫ _) = _
  rw [← Category.assoc, ← Category.assoc,
    Category.assoc i.hom, CofiberDiagrams.lift_inclusion]
  rfl

lemma quotientOriginalDiagrams_cofiber :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalDiagrams p q i r ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right Q.obj ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) =
        (i.hom ≫ cofiber p q) ≫ r.hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalDiagrams, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.postcomp_cofiber,
    ← Category.assoc, ← Category.assoc]
  have he := CofiberDiagrams.lift_right_target (laxCategory p q).obj (arrow p q)
  calc
    _ = (i.hom ≫ ((CofiberDiagrams.lift (laxCategory p q).obj (arrow p q) ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right (laxCategory p q).obj) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) ≫ r.hom := by
      simp only [Category.assoc]
    _ = _ := by rw [he]; rfl

lemma quotientSelectedDiagrams_cofiber :
    CofiberDiagrams.lift Q.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r) ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right Q.obj ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) =
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber Q.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r) := by
  rw [← Category.assoc, CofiberDiagrams.lift_right_target]

def quotientCofiberRelativeIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((i.hom ≫ cofiber p q) ≫ r.hom)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber Q.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientArrow p q i r)) :=
  (eqToIso (congrArg (fun f => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientOriginalDiagrams_cofiber p q i r))).symm ≪≫
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientDiagramComparison p q i r)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right Q.obj ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≪≫
  eqToIso (congrArg (fun f => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientSelectedDiagrams_cofiber p q i r))

lemma quotientCofiberRelativeIso_arrow :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiberRelativeIso p q i r).hom =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientRightTargetComparison p q i r) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.quotientCofiberRelativeIso
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv]
  rw [← Category.assoc, arrow_mk_comp_eqToHom, arrow_mk_eqToHom_comp,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIso_postcomp_hom]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
