module

public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeCAlgSource
public import SerrePositivity.EInfinity.BarrattEccles.CAlgUnderlyingDerivedComparison
public import SerrePositivity.EInfinity.ComplexLimits.ProbeDerivedComparison
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative

/-!
# 元の全複体源における実自由 probe の導来単位

概要：元の自由忘却単位と probe augmentation から全複体 nerve 上の同じ U 値への二胞体を得る。
方針：同じ probe の全比較を逆にし、元の単位円柱と全忘却比較を合成する。
規約：頂点ごとの任意の射の族で代用しない。
使われ方：D(R) の任意頂点の自由単位と comma 始対象の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.InfinityCategories DifferentialGraded
open scoped Simplicial
variable (A : Type u) [CommRing A]

def freeProbeUnitNatTrans : ComplexLimits.framedLimitProbeFunctor A ⟶
    freeProbeFunctor A ⋙ Operad.Algebra.forget (operad A) :=
  Functor.whiskerLeft (ComplexLimits.framedLimitProbeFunctor A)
    (operad A).freeAlgebraAdjunction.unit

lemma freeProbeUnderlyingNerve_eq :
    nerveMap (freeProbeFunctor A) ≫ nerveMap (Operad.Algebra.forget (operad A)) =
      nerveMap (freeProbeFunctor A ⋙ Operad.Algebra.forget (operad A)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro Γ
  change (Γ ⋙ freeProbeFunctor A) ⋙ Operad.Algebra.forget (operad A) = _
  exact Functor.assoc _ _ _

def freeProbeUnderlyingDerivedSourceIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (freeProbeCAlgSource A ≫ cAlgForgetDerived A)
    (nerveMap (freeProbeFunctor A ⋙ Operad.Algebra.forget (operad A)) ≫
      ComplexLimits.complexOrdinaryDerivedSource A) := by
  have e := (algebraCAlgSource_underlyingDerivedIso A).precomp (nerveMap (freeProbeFunctor A))
  have h : nerveMap (freeProbeFunctor A) ≫ algebraUnderlyingDerivedSource A =
      nerveMap (freeProbeFunctor A ⋙ Operad.Algebra.forget (operad A)) ≫
        ComplexLimits.complexOrdinaryDerivedSource A := by
    rw [algebraUnderlyingDerivedSource, ← Category.assoc, freeProbeUnderlyingNerve_eq]
  exact e ≪≫ eqToIso (congrArg (fun f => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) h)

def freeProbeUnitHomotopy : SSet.Homotopy
    (nerveMap (ComplexLimits.framedLimitProbeFunctor A) ≫
      ComplexLimits.complexOrdinaryDerivedSource A)
    (nerveMap (freeProbeFunctor A ⋙ Operad.Algebra.forget (operad A)) ≫
      ComplexLimits.complexOrdinaryDerivedSource A) :=
  ComplexLimits.complexOrdinaryDerivedNatTransHomotopy A (freeProbeUnitNatTrans A)

lemma freeProbeUnitHomotopy_component (X : Complex A) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (freeProbeUnitHomotopy A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)).edge =
      ((nerve.edgeMk ((freeProbeUnitNatTrans A).app X)).map
        (ComplexLimits.complexOrdinaryDerivedSource A)).edge :=
  ComplexLimits.complexOrdinaryDerivedNatTransHomotopy_component A (freeProbeUnitNatTrans A) X

def freeProbeUnitHom : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom
    (nerveMap (ComplexLimits.framedLimitProbeFunctor A) ≫
      ComplexLimits.complexOrdinaryDerivedSource A)
    (nerveMap (freeProbeFunctor A ⋙ Operad.Algebra.forget (operad A)) ≫
      ComplexLimits.complexOrdinaryDerivedSource A) :=
  Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (freeProbeUnitHomotopy A))

def freeProbeDerivedUnit : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (ComplexLimits.complexOrdinaryDerivedSource A)
    (freeProbeCAlgSource A ≫ cAlgForgetDerived A) :=
  (ComplexLimits.complexProbeDerivedSourceIso A).inv ≫ freeProbeUnitHom A ≫
    (freeProbeUnderlyingDerivedSourceIso A).inv

lemma freeProbeDerivedUnit_recovery :
    (ComplexLimits.complexProbeDerivedSourceIso A).hom ≫ freeProbeDerivedUnit A ≫
      (freeProbeUnderlyingDerivedSourceIso A).hom = freeProbeUnitHom A := by
  simp only [freeProbeDerivedUnit, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

end SerrePositivity.EInfinity.BarrattEccles
