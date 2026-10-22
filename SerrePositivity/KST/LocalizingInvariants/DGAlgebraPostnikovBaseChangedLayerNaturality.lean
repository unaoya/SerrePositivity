module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovExtensionBaseChangeMap

/-!
概要：底変更した標準 Postnikov 層の比較と包含は、元の代数射の層射に自然である。
方針：元の kernel 同型と標準層比較の可換式を使い、元の実包含を回収する。
規約：underlying 複体の実自然性。使われ方：元の π₂ 係数の逆の貼合せ。
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

lemma postnikovBaseChangedLayerToKernel_naturality :
    postnikovLayerMap R f n ≫ postnikovBaseChangedLayerToKernel R B n d =
      postnikovBaseChangedLayerToKernel R A n b ≫ postnikovBaseChangedKernelMap R f n b d v hs := by
  have hA : postnikovBaseChangedLayerToKernel R A n b ≫
      (postnikovBaseChangedKernelIso R A n b).hom = postnikovLayerToKernel R A n := by
    change (_ ≫ (postnikovBaseChangedKernelIso R A n b).inv) ≫ _ = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hB : postnikovBaseChangedLayerToKernel R B n d ≫
      (postnikovBaseChangedKernelIso R B n d).hom = postnikovLayerToKernel R B n := by
    change (_ ≫ (postnikovBaseChangedKernelIso R B n d).inv) ≫ _ = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_mono (postnikovBaseChangedKernelIso R B n d).hom).1
  rw [Category.assoc, hB, Category.assoc, postnikovBaseChangedKernelIso_naturality,
    ← Category.assoc, hA]
  exact postnikovLayerToKernel_naturality R f n

lemma postnikovBaseChangedLayerMap_inclusion :
    postnikovLayerMap R f n ≫ postnikovBaseChangedLayerInclusion R B n d =
      postnikovBaseChangedLayerInclusion R A n b ≫
        (postnikovExtensionBaseChangeMap R f n b d v hs).hom := by
  rw [postnikovBaseChangedLayerInclusion, postnikovBaseChangedLayerInclusion,
    ← Category.assoc, postnikovBaseChangedLayerToKernel_naturality R f n b d v hs,
    Category.assoc, postnikovBaseChangedKernelMap_inclusion, ← Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
