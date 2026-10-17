module
public import SerrePositivity.DifferentialGraded.Morita.PerfectQuasiEquivalenceTriangles
public import SerrePositivity.DifferentialGraded.Perfect.SmallEnhancementTriangulated

/-! # U16bとU13の小さい主dg enhancementの比較

実際の導来延長のPerf制限をU13の既存同値で小さいH⁰へ運び、比較正方形を保つ。
このH⁰の運搬を新たなdg関手の構成と同一視しない。dgの証拠は入力FのQuasiEquivalenceである。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)
local instance : (quasiEquivalencePerfectExtension A D E F).CommShift ℤ :=
  quasiEquivalencePerfectExtensionCommShift A D E F
local instance (hF : QuasiEquivalence F) :
    (quasiEquivalencePerfectEquivalence A D E F hF).functor.CommShift ℤ :=
  quasiEquivalencePerfectExtensionCommShift A D E F
local instance (hF : QuasiEquivalence F) :
    (quasiEquivalencePerfectEquivalence A D E F hF).inverse.CommShift ℤ :=
  quasiEquivalencePerfectRestrictionCommShift A D E F hF
local instance (hF : QuasiEquivalence F) :
    (quasiEquivalencePerfectEquivalence A D E F hF).CommShift ℤ :=
  quasiEquivalencePerfectCommShift A D E F hF
local instance (hF : QuasiEquivalence F) :
    (quasiEquivalencePerfectEquivalence A D E F hF).IsTriangulated :=
  quasiEquivalencePerfectIsTriangulated A D E F hF

def quasiEquivalenceSmallPerfectHomotopyEquivalence (hF : QuasiEquivalence F) :
    SmallPerfectDGHomotopyCategoryOver A D Set.univ ≌
      SmallPerfectDGHomotopyCategoryOver A E Set.univ :=
  ((smallPerfectDGModuleHomotopyEquivalence A D Set.univ).trans
    (quasiEquivalencePerfectEquivalence A D E F hF)).trans
      (smallPerfectDGModuleHomotopyEquivalence A E Set.univ).symm

instance quasiEquivalenceSmallPerfectHomotopyFunctorCommShift (hF : QuasiEquivalence F) :
    (quasiEquivalenceSmallPerfectHomotopyEquivalence A D E F hF).functor.CommShift ℤ :=
  by
    unfold quasiEquivalenceSmallPerfectHomotopyEquivalence
    infer_instance

instance quasiEquivalenceSmallPerfectHomotopyInverseCommShift (hF : QuasiEquivalence F) :
    (quasiEquivalenceSmallPerfectHomotopyEquivalence A D E F hF).inverse.CommShift ℤ :=
  by
    unfold quasiEquivalenceSmallPerfectHomotopyEquivalence
    infer_instance

instance quasiEquivalenceSmallPerfectHomotopyCommShift (hF : QuasiEquivalence F) :
    (quasiEquivalenceSmallPerfectHomotopyEquivalence A D E F hF).CommShift ℤ := by
  unfold quasiEquivalenceSmallPerfectHomotopyEquivalence
  infer_instance

instance quasiEquivalenceSmallPerfectHomotopyIsTriangulated (hF : QuasiEquivalence F) :
    (quasiEquivalenceSmallPerfectHomotopyEquivalence A D E F hF).IsTriangulated := by
  unfold quasiEquivalenceSmallPerfectHomotopyEquivalence
  infer_instance

def quasiEquivalenceSmallPerfectComparisonIso (hF : QuasiEquivalence F) :
    (quasiEquivalenceSmallPerfectHomotopyEquivalence A D E F hF).functor ⋙
        smallPerfectDGModuleToPerfect A E Set.univ ≅
      smallPerfectDGModuleToPerfect A D Set.univ ⋙ quasiEquivalencePerfectExtension A D E F :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (smallPerfectDGModuleHomotopyEquivalence A E Set.univ).counitIso ≪≫
      Functor.rightUnitor _

instance quasiEquivalenceSmallPerfectComparisonCommShift (hF : QuasiEquivalence F) :
    NatTrans.CommShift (quasiEquivalenceSmallPerfectComparisonIso A D E F hF).hom ℤ := by
  change NatTrans.CommShift
    ((Functor.associator
      ((smallPerfectDGModuleHomotopyEquivalence A D Set.univ).functor ⋙
        (quasiEquivalencePerfectEquivalence A D E F hF).functor)
      (smallPerfectDGModuleHomotopyEquivalence A E Set.univ).inverse
      (smallPerfectDGModuleHomotopyEquivalence A E Set.univ).functor).hom ≫
    Functor.whiskerLeft _ (smallPerfectDGModuleHomotopyEquivalence A E Set.univ).counitIso.hom ≫
    (Functor.rightUnitor _).hom) ℤ
  infer_instance

def quasiEquivalenceSmallPerfectComparisonTriangleIso (hF : QuasiEquivalence F) :
    (quasiEquivalenceSmallPerfectHomotopyEquivalence A D E F hF).functor.mapTriangle ⋙
        (smallPerfectDGModuleToPerfect A E Set.univ).mapTriangle ≅
      (smallPerfectDGModuleToPerfect A D Set.univ).mapTriangle ⋙
        (quasiEquivalencePerfectExtension A D E F).mapTriangle :=
  (Functor.mapTriangleCompIso _ _).symm ≪≫
    Functor.mapTriangleIso (quasiEquivalenceSmallPerfectComparisonIso A D E F hF) ≪≫
    Functor.mapTriangleCompIso _ _

end SerrePositivity.DifferentialGraded
