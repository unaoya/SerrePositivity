module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionLeftUnitComputation
public import Mathlib.Data.ZMod.Basic

/-! # 全導来bimodule合成の左右単位と解像度比較の監査 -/
@[expose] public section
noncomputable section
universe u v w z
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

example (hC : localHomKFlat A C) :
    (derivedBimoduleComposeFunctor A B C C hC).obj
        ((bimoduleToDerived A C C).obj (rightKFlatDiagonal A C).obj) ≅
      𝟭 (DerivedBimoduleCategory A B C) :=
  derivedBimoduleRightUnitIso A B C hC

example (hC : localHomKFlat A C) :
    derivedBimoduleLeftUnitFunctor A B C hC ≅ 𝟭 (DerivedBimoduleCategory A B C) :=
  derivedBimoduleLeftUnitIso A B C hC

example (hC : localHomKFlat A C) (Q : BimoduleCategory A B C)
    (R : RightKFlatBimoduleCategory A B C) (q : R.obj ⟶ Q)
    (hq : BimoduleCategory.quasiIso A B C q) :
    (derivedBimoduleLeftUnitIso A B C hC).hom.app ((bimoduleToDerived A B C).obj Q) =
      (derivedBimoduleLeftUnitResolutionIso A B C hC Q R q hq).hom :=
  derivedBimoduleLeftUnitIso_resolution_app A B C hC Q R q hq

-- 同じ対象の二つの解像度に対し、解像度間の射を選ばず比較できる。
example (hC : localHomKFlat A C) (Q : BimoduleCategory A B C)
    (R S : RightKFlatBimoduleCategory A B C) (q : R.obj ⟶ Q) (r : S.obj ⟶ Q)
    (hq : BimoduleCategory.quasiIso A B C q) (hr : BimoduleCategory.quasiIso A B C r) :
    (derivedBimoduleLeftUnitResolutionIso A B C hC Q R q hq).hom =
      (derivedBimoduleLeftUnitResolutionIso A B C hC Q S r hr).hom :=
  (derivedBimoduleLeftUnitIso_resolution_app A B C hC Q R q hq).symm.trans
    (derivedBimoduleLeftUnitIso_resolution_app A B C hC Q S r hr)

example (hE : localHomKFlat A E) {Q Q' : BimoduleCategory A C E}
    (R S : RightKFlatBimoduleCategory A C E) (q : R.obj ⟶ Q) (r : S.obj ⟶ Q')
    (hq : BimoduleCategory.quasiIso A C E q) (hr : BimoduleCategory.quasiIso A C E r)
    (f : Q ⟶ Q') (g : R ⟶ S)
    (h : (bimoduleToDerived A C E).map q ≫ (bimoduleToDerived A C E).map f =
      (bimoduleToDerived A C E).map g.hom ≫ (bimoduleToDerived A C E).map r) :
    (derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map f) ≫
        (derivedBimoduleComposeResolutionComputation A B C E hE Q' S r hr).hom =
      (derivedBimoduleComposeResolutionComputation A B C E hE Q R q hq).hom ≫
        derivedComposeWithMap A B C E R.property S.property g.hom :=
  derivedBimoduleComposeResolutionComputation_naturality A B C E hE R S q r hq hr f g h

example (B : Type v) (C : Type w) [DGCategory (ZMod 2) B] [DGCategory (ZMod 2) C]
    [Small.{0} B] [Small.{0} C] (hC : localHomKFlat (ZMod 2) C) :
    derivedBimoduleLeftUnitFunctor (ZMod 2) B C hC ≅
      𝟭 (DerivedBimoduleCategory (ZMod 2) B C) :=
  derivedBimoduleLeftUnitIso (ZMod 2) B C hC

#print axioms derivedBimoduleComposeResolutionComputation_fac
#print axioms derivedBimoduleComposeResolutionComputation_self
#print axioms derivedBimoduleComposeResolutionComputation_naturality
#print axioms rightKFlatDiagonal
#print axioms derivedBimoduleRightUnitIso
#print axioms derivedBimoduleRightUnitIso_base_app
#print axioms derivedBimoduleLeftUnitFunctor
#print axioms derivedBimoduleLeftUnitResolutionIso
#print axioms derivedBimoduleLeftUnitResolutionIso_naturality
#print axioms derivedBimoduleLeftUnitBaseIso
#print axioms derivedBimoduleLeftUnitBaseIso_naturality
#print axioms derivedBimoduleLeftUnitLocalizedIso
#print axioms derivedBimoduleLeftUnitIso
#print axioms derivedBimoduleLeftUnitIso_base_app
#print axioms derivedBimoduleLeftUnitResolutionIso_self
#print axioms derivedBimoduleLeftUnitIso_kFlat_base_app
#print axioms derivedBimoduleLeftUnitResolutionIso_fac
#print axioms derivedBimoduleLeftUnitIso_resolution_app
