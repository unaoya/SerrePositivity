module
public import SerrePositivity.DifferentialGraded.Resolution.Coherence
public import Mathlib.Data.ZMod.Basic

/-! # 指定dg圏解像度と解像度版の導来bimodule合成の監査 -/
@[expose] public section
noncomputable section
universe u v w z v' w' z'
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] {B : Type v} {C : Type w} {E : Type z}
  [DGCategory A B] [DGCategory A C] [DGCategory A E]

-- 元のB/C/Eにsmallnessやlocal HomのK-flat性を課さない。
-- 解像度の存在を主張せず、具体的な指定データP/Q/Rを入力する。
example (P : KFlatDGResolution.{u, v, v'} A B) (Q : KFlatDGResolution.{u, w, w'} A C)
    (R : KFlatDGResolution.{u, z, z'} A E) :
    ResolutionBimodule.DerivedCategory A Q R ⥤
      (ResolutionBimodule.DerivedCategory A P Q ⥤ ResolutionBimodule.DerivedCategory A P R) :=
  ResolutionBimodule.composeFunctor A P Q R

example (P : KFlatDGResolution.{u, v, v'} A B) (Q : KFlatDGResolution.{u, w, w'} A C)
    (R : KFlatDGResolution.{u, z, z'} A E) (M : ResolutionBimodule.DerivedCategory A Q R) :
    (ResolutionBimodule.associator A P Q Q R (ResolutionBimodule.diagonal A Q) M).hom ≫
        (ResolutionBimodule.composeFunctor A P Q R).map
          ((ResolutionBimodule.leftUnitIso A Q R).hom.app M) =
      Functor.whiskerRight (ResolutionBimodule.rightUnitIso A P Q).hom
        ((ResolutionBimodule.composeFunctor A P Q R).obj M) :=
  ResolutionBimodule.triangle A P Q R M

example [Small.{u} B] [Small.{u} C] [Small.{u} E]
    (hB : localHomKFlat A B) (hC : localHomKFlat A C) (hE : localHomKFlat A E) :
    ResolutionBimodule.composeFunctor A (KFlatDGResolution.refl A B hB)
        (KFlatDGResolution.refl A C hC) (KFlatDGResolution.refl A E hE) =
      derivedBimoduleComposeFunctor A B C E hE :=
  ResolutionBimodule.composeFunctor_refl A hB hC hE

example (B : Type v) (C : Type w) [DGCategory (ZMod 2) B] [DGCategory (ZMod 2) C]
    (P : KFlatDGResolution.{0, v, v'} (ZMod 2) B)
    (Q : KFlatDGResolution.{0, w, w'} (ZMod 2) C) :
    (ResolutionBimodule.composeFunctor (ZMod 2) P Q Q).obj
        (ResolutionBimodule.diagonal (ZMod 2) Q) ≅
      𝟭 (ResolutionBimodule.DerivedCategory (ZMod 2) P Q) :=
  ResolutionBimodule.rightUnitIso (ZMod 2) P Q

#print axioms KFlatDGResolution
#print axioms KFlatDGResolution.refl
#print axioms KFlatDGResolution.ofQuasiEquivalence
#print axioms KFlatDGResolution.postcompose
#print axioms ResolutionBimodule.DerivedCategory
#print axioms ResolutionBimodule.diagonal
#print axioms ResolutionBimodule.composeFunctor
#print axioms ResolutionBimodule.rightUnitIso
#print axioms ResolutionBimodule.leftUnitFunctor
#print axioms ResolutionBimodule.leftUnitIso
#print axioms ResolutionBimodule.associator
#print axioms ResolutionBimodule.triangle
#print axioms ResolutionBimodule.composeFunctor_refl
#print axioms ResolutionBimodule.pentagon
