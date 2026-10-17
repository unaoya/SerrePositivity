module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonGraphSquare
public import SerrePositivity.DifferentialGraded.Verdier.KaroubiFunctorSquare
public import SerrePositivity.DifferentialGraded.Morita.PerfectQuasiEquivalenceTriangles

/-! # 誘導 Verdier 関手・Karoubi 完備化・perfect enhancement と graph 作用の自然性 -/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents

section General
variable {C C' P P' : Type*} [Category* C] [Category* C'] [Category* P] [Category* P']
  (e : C ≌ P) (e' : C' ≌ P') (F : C ⥤ C') (T : P ⥤ P')

/-- 比較同値の順方向の正方形から、逆方向の正方形を得る。 -/
def equivalenceInverseSquare (α : F ⋙ e'.functor ≅ e.functor ⋙ T) :
    e.inverse ⋙ F ≅ T ⋙ e'.inverse :=
  ((whiskeringRight _ _ _).obj e'.functor).preimageIso
    (Functor.associator _ _ _ ≪≫ isoWhiskerLeft e.inverse α ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e.counitIso T ≪≫
      Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm ≪≫
      isoWhiskerLeft T e'.counitIso.symm ≪≫ (Functor.associator _ _ _).symm)
end General

namespace DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

local instance graphPerfectSquareExtensionCommShift :
    (quasiEquivalencePerfectExtension A D E F).CommShift ℤ :=
  quasiEquivalencePerfectExtensionCommShift A D E F
local instance graphPerfectSquareExtensionIsTriangulated :
    (quasiEquivalencePerfectExtension A D E F).IsTriangulated :=
  quasiEquivalencePerfectExtensionIsTriangulated A D E F

def graphTriaPerfectSquare :
    graphTriaFunctor A D E F ⋙ triaToPerfect A E ≅
      triaToPerfect A D ⋙ quasiEquivalencePerfectExtension A D E F := Iso.refl _

def graphKaroubiPerfectSquare :
    (functorExtension₂ _ _).obj (graphTriaFunctor A D E F) ⋙
        finiteCellKaroubiToPerfect A E Set.univ ≅
      finiteCellKaroubiToPerfect A D Set.univ ⋙ quasiEquivalencePerfectExtension A D E F :=
  triaKaroubiPerfectSquare A D E _ _ (graphTriaPerfectSquare A D E F)

variable (S : Set D) (T : Set E) (hF : ∀ d ∈ S, F.obj d ∈ T)
  (hD : localKFlat A D S) (hE : localKFlat A E T)

/-- 元の tria 上で誘導してから、指定 Karoubi 完備化を取った関手。 -/
def graphCompletedVerdierFunctor : CompletedTriaQuotient A D S ⥤ CompletedTriaQuotient A E T :=
  (functorExtension₂ _ _).obj (graphVerdierFunctor A D E F S T hF)

instance graphCompletedVerdierFunctorCommShift :
    (graphCompletedVerdierFunctor A D E F S T hF).CommShift ℤ := by
  dsimp [graphCompletedVerdierFunctor]
  infer_instance
instance graphCompletedVerdierFunctorIsTriangulated :
    (graphCompletedVerdierFunctor A D E F S T hF).IsTriangulated := by
  dsimp [graphCompletedVerdierFunctor]
  infer_instance

/-- 局所商比較の完備化は、実際に誘導した完備 Verdier 関手と可換する。 -/
def graphCompletedVerdierSquare :
    graphCompletedVerdierFunctor A D E F S T hF ⋙
        (localCompletedQuotientEquivalence A E T hE).functor ≅
      (localCompletedQuotientEquivalence A D S hD).functor ⋙
        (functorExtension₂ _ _).obj
          (graphTriaFunctor A (QuotientObject D S) (QuotientObject E T)
            (quotientDGFunctor A D E F S T hF)) :=
  karoubiFunctorSquare _ _ (graphLocalVerdierSquare A D E F S T hF)

/-- 完備商から主 Perf への、既存の二つの同値の合成。 -/
def graphCompletedPerfectComparison : CompletedTriaQuotient A D S ≌
    PerfectModuleCategory A (QuotientObject D S) :=
  (localCompletedQuotientEquivalence A D S hD).trans
    (finiteCellKaroubiPerfectEquivalence A (QuotientObject D S) Set.univ)

def graphCompletedPerfectSquare :
    graphCompletedVerdierFunctor A D E F S T hF ⋙
        (graphCompletedPerfectComparison A E T hE).functor ≅
      (graphCompletedPerfectComparison A D S hD).functor ⋙
        quasiEquivalencePerfectExtension A (QuotientObject D S) (QuotientObject E T)
          (quotientDGFunctor A D E F S T hF) :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (graphCompletedVerdierSquare A D E F S T hF hD hE) _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (graphKaroubiPerfectSquare A (QuotientObject D S) (QuotientObject E T)
      (quotientDGFunctor A D E F S T hF)) ≪≫ (Functor.associator _ _ _).symm

/-- 実際の商 dg 関手の導来 graph 作用を、既存 enhancement の H⁰ へ運ぶ。 -/
def graphQuotientPerfectHomotopyFunctor :
    PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ⥤
      PerfectDGHomotopyCategoryOver A (QuotientObject E T) Set.univ :=
  (perfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).functor ⋙
    quasiEquivalencePerfectExtension A (QuotientObject D S) (QuotientObject E T)
      (quotientDGFunctor A D E F S T hF) ⋙
    (perfectDGModuleHomotopyEquivalence A (QuotientObject E T) Set.univ).inverse

instance graphQuotientPerfectHomotopyFunctorCommShift :
    (graphQuotientPerfectHomotopyFunctor A D E F S T hF).CommShift ℤ := by
  dsimp [graphQuotientPerfectHomotopyFunctor]
  infer_instance
instance graphQuotientPerfectHomotopyFunctorIsTriangulated :
    (graphQuotientPerfectHomotopyFunctor A D E F S T hF).IsTriangulated := by
  dsimp [graphQuotientPerfectHomotopyFunctor]
  infer_instance

def graphQuotientPerfectHomotopySquare :
    graphQuotientPerfectHomotopyFunctor A D E F S T hF ⋙
        (perfectDGModuleHomotopyEquivalence A (QuotientObject E T) Set.univ).functor ≅
      (perfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).functor ⋙
        quasiEquivalencePerfectExtension A (QuotientObject D S) (QuotientObject E T)
          (quotientDGFunctor A D E F S T hF) :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (perfectDGModuleHomotopyEquivalence A (QuotientObject E T)
      Set.univ).counitIso ≪≫ Functor.rightUnitor _)

instance graphQuotientPerfectHomotopySquareCommShift :
    NatTrans.CommShift (graphQuotientPerfectHomotopySquare A D E F S T hF).hom ℤ := by
  dsimp only [graphQuotientPerfectHomotopySquare, Iso.trans_hom, isoWhiskerLeft_hom]
  infer_instance

def graphQuotientPerfectHomotopySquareTriangle :=
  Functor.mapTriangleIso (graphQuotientPerfectHomotopySquare A D E F S T hF)

/-- 指定された局所 perfect enhancement 比較そのものの、graph 作用に関する自然性。 -/
def graphLocalPerfectSquare :
    (localPerfectQuotientEquivalence A D S hD).functor ⋙
        graphCompletedVerdierFunctor A D E F S T hF ≅
      graphQuotientPerfectHomotopyFunctor A D E F S T hF ⋙
        (localPerfectQuotientEquivalence A E T hE).functor :=
  Functor.associator
      (perfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).functor
      (graphCompletedPerfectComparison A D S hD).inverse
      (graphCompletedVerdierFunctor A D E F S T hF) ≪≫
    isoWhiskerLeft _ (equivalenceInverseSquare
      (graphCompletedPerfectComparison A D S hD) (graphCompletedPerfectComparison A E T hE)
      _ _ (graphCompletedPerfectSquare A D E F S T hF hD hE)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (graphQuotientPerfectHomotopySquare A D E F S T hF).symm _ ≪≫
    Functor.associator _ _ _
end DGQuotient
end SerrePositivity.DifferentialGraded
