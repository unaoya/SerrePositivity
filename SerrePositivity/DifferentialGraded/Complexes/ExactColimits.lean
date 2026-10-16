module
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # 非有界複体のexactな余極限とacyclic性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u w w'
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] {J : Type w} [Category.{w'} J] [Small.{u} J]

/-- 非有界複体の図式を複体の各次数にある図式へ転置する。 -/
def complexDiagramTranspose (F : J ⥤ Complex A) : CochainComplex (J ⥤ ModuleCat.{u} A) ℤ where
  X i := F ⋙ eval (ModuleCat.{u} A) (.up ℤ) i
  d i j := { app := fun x => (F.obj x).d i j
             naturality := fun _ _ f => (F.map f).comm i j }
  shape i j h := by
    apply NatTrans.ext
    funext x
    exact (F.obj x).shape i j h
  d_comp_d' i j k _ _ := by
    apply NatTrans.ext
    funext x
    exact (F.obj x).d_comp_d i j k

omit [Small.{u} J] in
/-- 対象ごとのacyclic性は転置した関手複体のacyclic性を与える。 -/
lemma complexDiagramTranspose_acyclic (F : J ⥤ Complex A) (h : ∀ j, (F.obj j).Acyclic) :
    (complexDiagramTranspose A F).Acyclic := by
  intro n
  apply (exactAt_iff_isZero_homology _ n).2
  apply (Functor.isZero_iff _).2
  intro j
  exact IsZero.of_iso ((h j n).isZero_homology)
    (((complexDiagramTranspose A F).sc n).mapHomologyIso
      ((evaluation J (ModuleCat.{u} A)).obj j)).symm

variable [HasColimitsOfShape J (ModuleCat.{u} A)] [HasExactColimitsOfShape J (ModuleCat.{u} A)]

/-- 対象ごとacyclicな非有界複体のexactな余極限はacyclic。 -/
lemma complex_colimit_acyclic (F : J ⥤ Complex A) (h : ∀ j, (F.obj j).Acyclic) :
    (colimit F).Acyclic := by
  let K := complexDiagramTranspose A F
  let L := ((colim : (J ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A).mapHomologicalComplex (.up ℤ)).obj K
  have hK := complexDiagramTranspose_acyclic A F h
  have hL : L.Acyclic := by
    intro n
    apply (exactAt_iff_isZero_homology _ n).2
    exact IsZero.of_iso
      ((colim : (J ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A).map_isZero ((hK n).isZero_homology))
      ((K.sc n).mapHomologyIso (colim : (J ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A))
  let e : L ≅ colimit F :=
    IsColimit.coconePointUniqueUpToIso (isColimitCoconeOfHasColimitEval F) (colimit.isColimit F)
  intro n
  exact (hL n).of_iso e

end SerrePositivity.DifferentialGraded
