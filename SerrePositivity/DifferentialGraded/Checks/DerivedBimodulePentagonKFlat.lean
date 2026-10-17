module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionPentagonKFlat
public import Mathlib.Data.ZMod.Basic

/-! # K-flat三因子上の全導来五角図式と両経路の比較の監査 -/
@[expose] public section
noncomputable section
universe u v w z t x
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F] [Small.{u} G]

-- 既存の固定因子関手ではなく、全導来関手の結合同型で作った両経路の一致。
example (hE : localHomKFlat A E) (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    derivedBimodulePentagonShort A B C E F G hE hF hG
        ((bimoduleToDerived A C E).obj Q.obj) ((bimoduleToDerived A E F).obj R.obj)
        ((bimoduleToDerived A F G).obj S.obj) =
      derivedBimodulePentagonLong A B C E F G hE hF hG
        ((bimoduleToDerived A C E).obj Q.obj) ((bimoduleToDerived A E F).obj R.obj)
        ((bimoduleToDerived A F G).obj S.obj) :=
  derivedBimodulePentagon_kFlat A B C E F G hE hF hG Q R S

example (hE : localHomKFlat A E) (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) (P : DerivedBimoduleCategory A B C) :
    (derivedBimodulePentagonShort A B C E F G hE hF hG
        ((bimoduleToDerived A C E).obj Q.obj) ((bimoduleToDerived A E F).obj R.obj)
        ((bimoduleToDerived A F G).obj S.obj)).app P =
      (derivedBimodulePentagonLong A B C E F G hE hF hG
        ((bimoduleToDerived A C E).obj Q.obj) ((bimoduleToDerived A E F).obj R.obj)
        ((bimoduleToDerived A F G).obj S.obj)).app P :=
  NatTrans.congr_app (derivedBimodulePentagon_kFlat A B C E F G hE hF hG Q R S) P

example (B : Type v) (C : Type w) (E : Type z) (F : Type t) (G : Type x)
    [DGCategory (ZMod 2) B] [DGCategory (ZMod 2) C] [DGCategory (ZMod 2) E]
    [DGCategory (ZMod 2) F] [DGCategory (ZMod 2) G]
    [Small.{0} B] [Small.{0} C] [Small.{0} E] [Small.{0} F] [Small.{0} G]
    (hE : localHomKFlat (ZMod 2) E) (hF : localHomKFlat (ZMod 2) F)
    (hG : localHomKFlat (ZMod 2) G) (Q : RightKFlatBimoduleCategory (ZMod 2) C E)
    (R : RightKFlatBimoduleCategory (ZMod 2) E F) (S : RightKFlatBimoduleCategory (ZMod 2) F G) :
    derivedBimodulePentagonShort (ZMod 2) B C E F G hE hF hG
        ((bimoduleToDerived (ZMod 2) C E).obj Q.obj) ((bimoduleToDerived (ZMod 2) E F).obj R.obj)
        ((bimoduleToDerived (ZMod 2) F G).obj S.obj) =
      derivedBimodulePentagonLong (ZMod 2) B C E F G hE hF hG
        ((bimoduleToDerived (ZMod 2) C E).obj Q.obj) ((bimoduleToDerived (ZMod 2) E F).obj R.obj)
        ((bimoduleToDerived (ZMod 2) F G).obj S.obj) :=
  derivedBimodulePentagon_kFlat (ZMod 2) B C E F G hE hF hG Q R S

#print axioms derivedBimoduleTripleLeftValueIso
#print axioms derivedBimoduleTripleRightValueIso
#print axioms derivedBimoduleTripleValueIso_associator
#print axioms derivedBimoduleTripleSourceIso
#print axioms derivedBimoduleTripleLeftFunctorIso
#print axioms derivedBimoduleTripleRightFunctorIso
#print axioms derivedBimoduleTripleFunctorIso_associator
#print axioms derivedBimodulePentagonShort_middle
#print axioms derivedBimodulePentagonShort_kFlat_fac
#print axioms derivedBimoduleTripleSourceAltIso
#print axioms derivedBimoduleTripleSourceAltIso_eq
#print axioms derivedBimodulePentagonLong_middle
#print axioms derivedBimodulePentagonLong_kFlat_fac
#print axioms derivedBimodulePentagon_kFlat
