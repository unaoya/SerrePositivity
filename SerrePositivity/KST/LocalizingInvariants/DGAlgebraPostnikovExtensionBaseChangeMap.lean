module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraExtensionBaseChangeKernelMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovBaseChangedLayer
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerMaps

/-!
概要：元の隣接拡大の射を、指定した二つの実下段射に沿う底変更へ移す。
方針：元の postnikovMap と遷移の自然性を使い、実 kernel 同型との可換式を保つ。
規約：元の下段射への同値仮定は不要。使われ方：元の二切断射の係数比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A B P Q : Mon (Complex R)}
  [A.X.IsStrictlyLE 0] [B.X.IsStrictlyLE 0] (f : A ⟶ B) (n : ℤ)
  (b : P ⟶ postnikov R A n) (d : Q ⟶ postnikov R B n) (v : P ⟶ Q)
  (hs : b ≫ postnikovMap R f n = v ≫ d)

def postnikovExtensionBaseChangeMap :
    postnikovExtensionBaseChange R A n b ⟶ postnikovExtensionBaseChange R B n d :=
  ExtensionBaseChange.map R b (postnikovTransition R A (n + 1) n (by omega)) d
    (postnikovTransition R B (n + 1) n (by omega)) v
    (postnikovMap R f (n + 1)) (postnikovMap R f n) hs
    (postnikovTransition_naturality R A f (n + 1) n (by omega)).symm

lemma postnikovExtensionBaseChangeMap_base :
    postnikovExtensionBaseChangeMap R f n b d v hs ≫ postnikovExtensionBaseChangeBase R B n d =
      postnikovExtensionBaseChangeBase R A n b ≫ v :=
  ExtensionBaseChange.map_base R _ _ _ _ _ _ _ _ _

lemma postnikovExtensionBaseChangeMap_upper :
    postnikovExtensionBaseChangeMap R f n b d v hs ≫ postnikovExtensionBaseChangeUpper R B n d =
      postnikovExtensionBaseChangeUpper R A n b ≫ postnikovMap R f (n + 1) :=
  ExtensionBaseChange.map_upper R _ _ _ _ _ _ _ _ _

def postnikovBaseChangedKernelMap : kernel (postnikovExtensionBaseChangeBase R A n b).hom ⟶
    kernel (postnikovExtensionBaseChangeBase R B n d).hom :=
  ExtensionBaseChange.kernelSquareMap R b (postnikovTransition R A (n + 1) n (by omega)) d
    (postnikovTransition R B (n + 1) n (by omega)) v
    (postnikovMap R f (n + 1)) (postnikovMap R f n) hs
    (postnikovTransition_naturality R A f (n + 1) n (by omega)).symm

lemma postnikovBaseChangedKernelMap_inclusion :
    postnikovBaseChangedKernelMap R f n b d v hs ≫
      kernel.ι (postnikovExtensionBaseChangeBase R B n d).hom =
        kernel.ι (postnikovExtensionBaseChangeBase R A n b).hom ≫
          (postnikovExtensionBaseChangeMap R f n b d v hs).hom :=
  ExtensionBaseChange.kernelSquareMap_inclusion R _ _ _ _ _ _ _ _ _

lemma postnikovBaseChangedKernelIso_naturality :
    postnikovBaseChangedKernelMap R f n b d v hs ≫ (postnikovBaseChangedKernelIso R B n d).hom =
      (postnikovBaseChangedKernelIso R A n b).hom ≫ postnikovKernelMap R f n := by
  have h := ExtensionBaseChange.kernelMap_naturality R b
    (postnikovTransition R A (n + 1) n (by omega)) d
    (postnikovTransition R B (n + 1) n (by omega)) v
    (postnikovMap R f (n + 1)) (postnikovMap R f n) hs
    (postnikovTransition_naturality R A f (n + 1) n (by omega)).symm
  have he : ExtensionBaseChange.kernelOriginalMap R
      (postnikovTransition R A (n + 1) n (by omega))
      (postnikovTransition R B (n + 1) n (by omega))
      (postnikovMap R f (n + 1)) (postnikovMap R f n)
      (postnikovTransition_naturality R A f (n + 1) n (by omega)).symm =
        postnikovKernelMap R f n := by
    apply (cancel_mono (postnikovKernelInclusion R B n)).1
    exact (ExtensionBaseChange.kernelOriginalMap_inclusion R _ _ _ _ _).trans
      (postnikovKernelMap_inclusion R f n).symm
  exact h.trans (congrArg (fun z => (postnikovBaseChangedKernelIso R A n b).hom ≫ z) he)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
