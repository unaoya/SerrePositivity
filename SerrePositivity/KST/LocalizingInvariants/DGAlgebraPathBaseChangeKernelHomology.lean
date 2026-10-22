module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathBaseChangeKernels
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraExtensionBaseChangeKernel

/-!
概要：元の底経路に沿う二つの実 kernel のホモロジーを、上段の射を保って比較する。
方針：同じ実共通 kernel への両準同型を反転する。
規約：底や上段の準同型性を仮定しない。使われ方：元の係数逆を同じ底へ移す。
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
  [P.X.IsStrictlyLE 0] [U.X.IsStrictlyLE 0] [Epi q.hom]

def kernelHomologyIso (j : ℤ) :
    (kernel (MonoidPullback.fst a q).hom).homology j ≅
      (kernel (MonoidPullback.fst b q).hom).homology j := by
  have := firstKernel_quasiIso R a q
  have := secondKernel_quasiIso R a b q w
  exact asIso (homologyMap (firstKernel R a q) j) ≪≫
    (asIso (homologyMap (secondKernel R a b q w) j)).symm

lemma kernelHomologyIso_upper (j : ℤ) :
    (kernelHomologyIso R a b q w j).hom ≫
      homologyMap (kernel.ι (MonoidPullback.fst b q).hom ≫ (MonoidPullback.snd b q).hom) j =
    homologyMap (kernel.ι (MonoidPullback.fst a q).hom ≫ (MonoidPullback.snd a q).hom) j := by
  have := secondKernel_quasiIso R a b q w
  let z := homologyMap
    (kernel.ι (nonpositiveBase R a q).hom ≫ (nonpositiveUpper R a q).hom) j
  have h₁ : homologyMap (firstKernel R a q) j ≫ z =
      homologyMap (kernel.ι (MonoidPullback.fst a q).hom ≫ (MonoidPullback.snd a q).hom) j :=
    (homologyMap_comp (firstKernel R a q)
      (kernel.ι (nonpositiveBase R a q).hom ≫ (nonpositiveUpper R a q).hom) j).symm.trans
      (congrArg (fun t => homologyMap t j) (firstKernel_upper R a q))
  have h₂ : homologyMap (secondKernel R a b q w) j ≫ z =
      homologyMap (kernel.ι (MonoidPullback.fst b q).hom ≫ (MonoidPullback.snd b q).hom) j :=
    (homologyMap_comp (secondKernel R a b q w)
      (kernel.ι (nonpositiveBase R a q).hom ≫ (nonpositiveUpper R a q).hom) j).symm.trans
      (congrArg (fun t => homologyMap t j) (secondKernel_upper R a b q w))
  change (homologyMap (firstKernel R a q) j ≫
    inv (homologyMap (secondKernel R a b q w) j)) ≫ _ = _
  exact moduleIsoSpan_comp _ _ _ _ z h₁ h₂

lemma kernelHomologyIso_original (j : ℤ) [Mono (homologyMap (kernel.ι q.hom) j)] :
    (kernelHomologyIso R a b q w j).hom ≫
      homologyMap (ExtensionBaseChange.kernelMap R b q) j =
        homologyMap (ExtensionBaseChange.kernelMap R a q) j := by
  have h₁ : homologyMap (ExtensionBaseChange.kernelMap R a q) j ≫
      homologyMap (kernel.ι q.hom) j =
      homologyMap (kernel.ι (MonoidPullback.fst a q).hom ≫ (MonoidPullback.snd a q).hom) j :=
    (homologyMap_comp (ExtensionBaseChange.kernelMap R a q) (kernel.ι q.hom) j).symm.trans
      (congrArg (fun t => homologyMap t j) (ExtensionBaseChange.kernelMap_inclusion R a q))
  have h₂ : homologyMap (ExtensionBaseChange.kernelMap R b q) j ≫
      homologyMap (kernel.ι q.hom) j =
      homologyMap (kernel.ι (MonoidPullback.fst b q).hom ≫ (MonoidPullback.snd b q).hom) j :=
    (homologyMap_comp (ExtensionBaseChange.kernelMap R b q) (kernel.ι q.hom) j).symm.trans
      (congrArg (fun t => homologyMap t j) (ExtensionBaseChange.kernelMap_inclusion R b q))
  apply (cancel_mono (homologyMap (kernel.ι q.hom) j)).1
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => (kernelHomologyIso R a b q w j).hom ≫ t) h₂).trans
      ((kernelHomologyIso_upper R a b q w j).trans h₁.symm))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathBaseChange
