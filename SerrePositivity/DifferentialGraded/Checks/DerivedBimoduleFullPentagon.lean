module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionPentagon
public import Mathlib.Data.ZMod.Basic

/-! # 全導来因子の五角恒等式とパラメータ族の監査 -/
@[expose] public section
noncomputable section
universe u v w z t x s s'
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F] [Small.{u} G]

example (hE : localHomKFlat A E) (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : DerivedBimoduleCategory A C E) (R : DerivedBimoduleCategory A E F)
    (S : DerivedBimoduleCategory A F G) :
    derivedBimodulePentagonShort A B C E F G hE hF hG Q R S =
      derivedBimodulePentagonLong A B C E F G hE hF hG Q R S :=
  derivedBimodulePentagon A B C E F G hE hF hG Q R S

example (hE : localHomKFlat A E) (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : DerivedBimoduleCategory A C E) (R : DerivedBimoduleCategory A E F)
    (S : DerivedBimoduleCategory A F G) (P : DerivedBimoduleCategory A B C) :
    (derivedBimodulePentagonShort A B C E F G hE hF hG Q R S).app P =
      (derivedBimodulePentagonLong A B C E F G hE hF hG Q R S).app P :=
  NatTrans.congr_app (derivedBimodulePentagon A B C E F G hE hF hG Q R S) P

-- パラメータ圏の対象・射宇宙はdg圏の対象宇宙やAの宇宙とは独立。
example {T : Type s} [Category.{s'} T] (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : T ⥤ DerivedBimoduleCategory A C E) (R : T ⥤ DerivedBimoduleCategory A E F)
    (S : T ⥤ DerivedBimoduleCategory A F G) :
    derivedBimoduleComposeFamily A C F G hG (derivedBimoduleComposeFamily A C E F hF Q R) S ≅
      derivedBimoduleComposeFamily A C E G hG Q (derivedBimoduleComposeFamily A E F G hG R S) :=
  derivedBimoduleInnerAssociatorFamily A C E F G hF hG Q R S

example (B : Type v) (C : Type w) (E : Type z) (F : Type t) (G : Type x)
    [DGCategory (ZMod 2) B] [DGCategory (ZMod 2) C] [DGCategory (ZMod 2) E]
    [DGCategory (ZMod 2) F] [DGCategory (ZMod 2) G]
    [Small.{0} B] [Small.{0} C] [Small.{0} E] [Small.{0} F] [Small.{0} G]
    (hE : localHomKFlat (ZMod 2) E) (hF : localHomKFlat (ZMod 2) F)
    (hG : localHomKFlat (ZMod 2) G) (Q : DerivedBimoduleCategory (ZMod 2) C E)
    (R : DerivedBimoduleCategory (ZMod 2) E F) (S : DerivedBimoduleCategory (ZMod 2) F G) :
    derivedBimodulePentagonShort (ZMod 2) B C E F G hE hF hG Q R S =
      derivedBimodulePentagonLong (ZMod 2) B C E F G hE hF hG Q R S :=
  derivedBimodulePentagon (ZMod 2) B C E F G hE hF hG Q R S

#print axioms compositionFamily
#print axioms compositionFamilyMap
#print axioms compositionFamilyAssociator
#print axioms derivedBimoduleComposeFamily
#print axioms derivedBimoduleAssociatorFamily
#print axioms derivedBimoduleInnerAssociatorFamily
#print axioms derivedBimodulePentagonShortFamily
#print axioms derivedBimodulePentagonLongFamily
#print axioms derivedBimodulePentagonShortFamily_app
#print axioms derivedBimodulePentagonLongFamily_app
#print axioms exists_rightKFlat_derived_iso
#print axioms derivedBimodulePentagon
