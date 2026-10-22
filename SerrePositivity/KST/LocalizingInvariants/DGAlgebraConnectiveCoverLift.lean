module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveCoverFunctor

/-!
概要：非正次数の元の実代数射を、標的の connective cover へ一意に持ち上げる。
方針：源の cover 包含の実逆と元の cover 関手を合成し、元の自然性で回収する。
規約：実単位・積と元の射を保持。使われ方：非正次数の roof の厳密な左三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

instance connectiveCoverInclusion_isIso (A : Mon (Complex R)) [A.X.IsStrictlyLE 0] :
    IsIso (connectiveCoverInclusion R A) := by
  have : IsIso ((Mon.forget (Complex R)).map (connectiveCoverInclusion R A)) := by
    change IsIso (A.X.ιTruncLE 0)
    infer_instance
  exact isIso_of_reflects_iso _ (Mon.forget (Complex R))

variable {A B : Mon (Complex R)} [A.X.IsStrictlyLE 0]

def connectiveCoverLift (f : A ⟶ B) : A ⟶ connectiveCover R B :=
  inv (connectiveCoverInclusion R A) ≫ connectiveCoverMap R f

lemma connectiveCoverLift_inclusion (f : A ⟶ B) :
    connectiveCoverLift R f ≫ connectiveCoverInclusion R B = f := by
  have hf : connectiveCoverMap R f ≫ connectiveCoverInclusion R B =
      connectiveCoverInclusion R A ≫ f := (connectiveCoverCounit R).naturality f
  rw [connectiveCoverLift, Category.assoc, hf, IsIso.inv_hom_id_assoc]

lemma connectiveCoverLift_unique (f : A ⟶ B) (g : A ⟶ connectiveCover R B)
    (hg : g ≫ connectiveCoverInclusion R B = f) : g = connectiveCoverLift R f := by
  have : Mono (connectiveCoverInclusion R B) :=
    (Mon.forget (Complex R)).mono_of_mono_map (by change Mono (coverInclusion R B); infer_instance)
  apply (cancel_mono (connectiveCoverInclusion R B)).1
  exact hg.trans (connectiveCoverLift_inclusion R f).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
