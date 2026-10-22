module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraExtensionBaseChangeMap

/-!
概要：底変更の実射が誘導する実 kernel 射を、元の kernel 射と厳密に比較する。
方針：元の実射影の可換式と kernel 包含の単射性を使う。
規約：ホモロジーだけの自然性に弱めない。使われ方：元の π₂ 射の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.ExtensionBaseChange
variable (R : Type u) [CommRing R] {P U B P' U' B' : Mon (Complex R)}
  (b : P ⟶ B) (q : U ⟶ B) (b' : P' ⟶ B') (q' : U' ⟶ B')
  (v : P ⟶ P') (u : U ⟶ U') (d : B ⟶ B')
  (hb : b ≫ d = v ≫ b') (hq : q ≫ d = u ≫ q')

def kernelSquareMap : kernel (base R b q).hom ⟶ kernel (base R b' q').hom :=
  kernel.map _ _ (map R b q b' q' v u d hb hq).hom v.hom
    (congrArg Mon.Hom.hom (map_base R b q b' q' v u d hb hq).symm)

lemma kernelSquareMap_inclusion : kernelSquareMap R b q b' q' v u d hb hq ≫
    kernel.ι (base R b' q').hom =
      kernel.ι (base R b q).hom ≫ (map R b q b' q' v u d hb hq).hom := kernel.lift_ι _ _ _

def kernelOriginalMap : kernel q.hom ⟶ kernel q'.hom :=
  kernel.map _ _ u.hom d.hom (congrArg Mon.Hom.hom hq)

lemma kernelOriginalMap_inclusion : kernelOriginalMap R q q' u d hq ≫ kernel.ι q'.hom =
    kernel.ι q.hom ≫ u.hom := kernel.lift_ι _ _ _

lemma kernelMap_naturality : kernelSquareMap R b q b' q' v u d hb hq ≫ kernelMap R b' q' =
    kernelMap R b q ≫ kernelOriginalMap R q q' u d hq := by
  have hu : (map R b q b' q' v u d hb hq).hom ≫ (upper R b' q').hom =
      (upper R b q).hom ≫ u.hom := congrArg Mon.Hom.hom (map_upper R b q b' q' v u d hb hq)
  apply (cancel_mono (kernel.ι q'.hom)).1
  rw [Category.assoc, kernelMap_inclusion, ← Category.assoc, kernelSquareMap_inclusion,
    Category.assoc, hu, ← Category.assoc, ← kernelMap_inclusion,
    Category.assoc (kernelMap R b q) (kernelOriginalMap R q q' u d hq) (kernel.ι q'.hom),
    kernelOriginalMap_inclusion]
  exact Category.assoc _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.ExtensionBaseChange
