module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathBaseChangeNonpositive
public import SerrePositivity.KST.LocalizingInvariants.CochainKernelMapQuasiIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraExtensionBaseChange

/-!
概要：経路に沿う共通底変更模型の実 kernel と両端の実 kernel を比較する。
方針：元の底射の厳密な一致を使い、全射正方形の kernel 準同型性を適用する。
規約：元の kernel 包含・上段への射を保持。使われ方：同じ底上での π₂ 係数比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathBaseChange
variable (R : Type u) [CommRing R] {P B U : Mon (Complex R)}
  (a b : P ⟶ B) (q : U ⟶ B) (w : Path.Witness R a b)
  [P.X.IsStrictlyLE 0] [U.X.IsStrictlyLE 0]

lemma nonpositiveBase_epi [Epi q.hom] : Epi (nonpositiveBase R a q).hom := by
  have : Epi (MonoidPullback.fst a q).hom := ExtensionBaseChange.base_epi R a q
  exact epi_of_epi_fac (congrArg Mon.Hom.hom (firstNonpositive_base R a q))

def firstKernel : kernel (MonoidPullback.fst a q).hom ⟶
    kernel (nonpositiveBase R a q).hom :=
  kernel.map _ _ (firstNonpositive R a q).hom (𝟙 P.X)
    ((Category.comp_id _).trans
      (congrArg Mon.Hom.hom (firstNonpositive_base R a q)).symm)

def secondKernel : kernel (MonoidPullback.fst b q).hom ⟶
    kernel (nonpositiveBase R a q).hom :=
  kernel.map _ _ (secondNonpositive R a b q w).hom (𝟙 P.X)
    ((Category.comp_id _).trans
      (congrArg Mon.Hom.hom (secondNonpositive_base R a b q w)).symm)

lemma firstKernel_inclusion : firstKernel R a q ≫ kernel.ι (nonpositiveBase R a q).hom =
    kernel.ι (MonoidPullback.fst a q).hom ≫ (firstNonpositive R a q).hom :=
  kernel.lift_ι _ _ _

lemma secondKernel_inclusion : secondKernel R a b q w ≫
    kernel.ι (nonpositiveBase R a q).hom =
      kernel.ι (MonoidPullback.fst b q).hom ≫ (secondNonpositive R a b q w).hom :=
  kernel.lift_ι _ _ _

lemma firstKernel_quasiIso [Epi q.hom] : QuasiIso (firstKernel R a q) := by
  have : Epi (MonoidPullback.fst a q).hom := ExtensionBaseChange.base_epi R a q
  have := nonpositiveBase_epi R a q
  exact cochainKernelMap_quasiIso (MonoidPullback.fst a q).hom
    (nonpositiveBase R a q).hom (firstNonpositive R a q).hom (𝟙 P.X)
    ((Category.comp_id _).trans
      (congrArg Mon.Hom.hom (firstNonpositive_base R a q)).symm)
    (firstNonpositive_quasiIso R a q) (quasiIso_of_isIso (𝟙 P.X))

lemma secondKernel_quasiIso [Epi q.hom] : QuasiIso (secondKernel R a b q w) := by
  have : Epi (MonoidPullback.fst b q).hom := ExtensionBaseChange.base_epi R b q
  have := nonpositiveBase_epi R a q
  exact cochainKernelMap_quasiIso (MonoidPullback.fst b q).hom
    (nonpositiveBase R a q).hom (secondNonpositive R a b q w).hom (𝟙 P.X)
    ((Category.comp_id _).trans
      (congrArg Mon.Hom.hom (secondNonpositive_base R a b q w)).symm)
    (secondNonpositive_quasiIso R a b q w) (quasiIso_of_isIso (𝟙 P.X))

lemma firstKernel_upper : firstKernel R a q ≫
    kernel.ι (nonpositiveBase R a q).hom ≫ (nonpositiveUpper R a q).hom =
      kernel.ι (MonoidPullback.fst a q).hom ≫ (MonoidPullback.snd a q).hom := by
  have hu : (firstNonpositive R a q).hom ≫ (nonpositiveUpper R a q).hom =
      (MonoidPullback.snd a q).hom :=
    congrArg Mon.Hom.hom (firstNonpositive_upper R a q)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ (nonpositiveUpper R a q).hom)
      (firstKernel_inclusion R a q)).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun t => kernel.ι (MonoidPullback.fst a q).hom ≫ t) hu)))

lemma secondKernel_upper : secondKernel R a b q w ≫
    kernel.ι (nonpositiveBase R a q).hom ≫ (nonpositiveUpper R a q).hom =
      kernel.ι (MonoidPullback.fst b q).hom ≫ (MonoidPullback.snd b q).hom := by
  have hu : (secondNonpositive R a b q w).hom ≫ (nonpositiveUpper R a q).hom =
      (MonoidPullback.snd b q).hom :=
    congrArg Mon.Hom.hom (secondNonpositive_upper R a b q w)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ (nonpositiveUpper R a q).hom)
      (secondKernel_inclusion R a b q w)).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun t => kernel.ι (MonoidPullback.fst b q).hom ≫ t) hu)))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathBaseChange
