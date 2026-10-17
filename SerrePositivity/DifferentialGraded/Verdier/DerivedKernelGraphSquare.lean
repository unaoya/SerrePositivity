module
public import SerrePositivity.DifferentialGraded.Verdier.GraphPerfectSquare
public import SerrePositivity.DifferentialGraded.Morita.KernelDerivedFunctor
public import SerrePositivity.DifferentialGraded.Morita.PerfectFunctoriality

/-! # 主導来 kernel 上の実際の graph 作用と局所 perfect 商比較

U16a の主局所化上の作用を使い、通常 bimodule の対象ごとの計算だけに留めない。
-/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory CategoryTheory.Functor Morita
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 主導来 graph kernel の実際の作用から、既存 graph 延長への関手自然同型。 -/
def derivedKernelGraphComparison :
    kernelDerivedTensor A D E (kernelGraph A D E F) ≅ dgDerivedExtension A D E F :=
  kernelDerivedTensorOnBimoduleIso A D E (BimoduleCategory.of A E D (functorGraph A D E F)) ≪≫
    eqToIso (kernelDerivedTensorOnBimodule_graph A D E F)

lemma derivedKernelGraph_perfect {X : DerivedModuleCategory A D} (hX : modulePerfect A D X) :
    modulePerfect A E ((kernelDerivedTensor A D E (kernelGraph A D E F)).obj X) :=
  (modulePerfect A E).prop_of_iso ((derivedKernelGraphComparison A D E F).app X).symm
    (dgDerivedExtension_perfect A D E F hX)

def derivedKernelGraphPerfectFunctor : PerfectModuleCategory A D ⥤ PerfectModuleCategory A E :=
  perfectFunctorRestriction A D E (kernelDerivedTensor A D E (kernelGraph A D E F))
    (fun _ hX => derivedKernelGraph_perfect A D E F hX)

def derivedKernelGraphPerfectComparison :
    derivedKernelGraphPerfectFunctor A D E F ≅ quasiEquivalencePerfectExtension A D E F :=
  perfectFunctorIso A D E _ _ (fun _ hX => derivedKernelGraph_perfect A D E F hX)
    (fun _ hX => dgDerivedExtension_perfect A D E F hX) (derivedKernelGraphComparison A D E F)

variable (S : Set D) (T : Set E) (hF : ∀ d ∈ S, F.obj d ∈ T)

/-- 主導来 graph kernel の作用そのものによる、全導来対象と射に自然な商正方形。 -/
def derivedKernelGraphQuotientSquare :
    kernelDerivedTensor A D (QuotientObject D S) (kernelGraph A D _ (inclusion A D S)) ⋙
        kernelDerivedTensor A (QuotientObject D S) (QuotientObject E T)
          (kernelGraph A _ _ (quotientDGFunctor A D E F S T hF)) ≅
      kernelDerivedTensor A D E (kernelGraph A D E F) ⋙
        kernelDerivedTensor A E (QuotientObject E T) (kernelGraph A E _ (inclusion A E T)) :=
  isoWhiskerRight (derivedKernelGraphComparison A D _ (inclusion A D S)) _ ≪≫
    isoWhiskerLeft _ (derivedKernelGraphComparison A _ _ (quotientDGFunctor A D E F S T hF)) ≪≫
    graphDerivedQuotientSquare A D E F S T hF ≪≫
    isoWhiskerLeft _ (derivedKernelGraphComparison A E _ (inclusion A E T)).symm ≪≫
    isoWhiskerRight (derivedKernelGraphComparison A D E F).symm _

def derivedKernelQuotientPerfectHomotopyFunctor :
    PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ⥤
      PerfectDGHomotopyCategoryOver A (QuotientObject E T) Set.univ :=
  (perfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).functor ⋙
    derivedKernelGraphPerfectFunctor A _ _ (quotientDGFunctor A D E F S T hF) ⋙
      (perfectDGModuleHomotopyEquivalence A (QuotientObject E T) Set.univ).inverse

def derivedKernelQuotientPerfectHomotopyComparison :
    derivedKernelQuotientPerfectHomotopyFunctor A D E F S T hF ≅
      graphQuotientPerfectHomotopyFunctor A D E F S T hF :=
  isoWhiskerLeft _ (isoWhiskerRight
    (derivedKernelGraphPerfectComparison A _ _ (quotientDGFunctor A D E F S T hF)) _)

/-- 主導来 kernel の graph 作用と、指定された局所 perfect enhancement 比較の正方形。 -/
def derivedKernelLocalPerfectSquare (hD : localKFlat A D S) (hE : localKFlat A E T) :
    (localPerfectQuotientEquivalence A D S hD).functor ⋙
        graphCompletedVerdierFunctor A D E F S T hF ≅
      derivedKernelQuotientPerfectHomotopyFunctor A D E F S T hF ⋙
        (localPerfectQuotientEquivalence A E T hE).functor :=
  graphLocalPerfectSquare A D E F S T hF hD hE ≪≫
    isoWhiskerRight (derivedKernelQuotientPerfectHomotopyComparison A D E F S T hF).symm _
end SerrePositivity.DifferentialGraded.DGQuotient
