module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerHomology

/-!
概要：元の dg 代数射に対する Postnikov 層・kernel 比較の自然性を証明する。
方針：smart 切断の自然性と kernel の一意性を使い、元の包含を保持する。
規約：ホモロジー同型だけから比較射を選ばない。使われ方：pro 系への層比較の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra

variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ)

def postnikovLayerMap : postnikovLayer R B n ⟶ postnikovLayer R C n :=
  CochainComplex.truncLEMap (postnikovMap R f (n + 1)).hom (-(n + 1))

lemma postnikovLayerMap_inclusion :
    postnikovLayerMap R f n ≫ postnikovLayerInclusion R C n =
      postnikovLayerInclusion R B n ≫ (postnikovMap R f (n + 1)).hom :=
  CochainComplex.ιTruncLE_naturality _ _

def postnikovKernelMap : postnikovKernel R B n ⟶ postnikovKernel R C n := by
  refine kernel.lift _
    (postnikovKernelInclusion R B n ≫ (postnikovMap R f (n + 1)).hom) ?_
  have ht := congrArg Mon.Hom.hom
    (postnikovTransition_naturality R B f (n + 1) n (by omega))
  change (postnikovMap R f (n + 1)).hom ≫
    (postnikovTransition R C (n + 1) n (by omega)).hom =
    (postnikovTransition R B (n + 1) n (by omega)).hom ≫ (postnikovMap R f n).hom at ht
  rw [Category.assoc, ht, ← Category.assoc]
  simp [postnikovKernelInclusion]

lemma postnikovKernelMap_inclusion :
    postnikovKernelMap R f n ≫ postnikovKernelInclusion R C n =
      postnikovKernelInclusion R B n ≫ (postnikovMap R f (n + 1)).hom :=
  kernel.lift_ι _ _ _

lemma postnikovLayerToKernel_naturality :
    postnikovLayerMap R f n ≫ postnikovLayerToKernel R C n =
      postnikovLayerToKernel R B n ≫ postnikovKernelMap R f n := by
  apply (cancel_mono (postnikovKernelInclusion R C n)).1
  rw [Category.assoc, postnikovLayerToKernel_inclusion, postnikovLayerMap_inclusion,
    Category.assoc, postnikovKernelMap_inclusion, ← Category.assoc,
    postnikovLayerToKernel_inclusion]

lemma postnikovLayerHomologyIso_naturality :
    homologyMap (postnikovLayerMap R f n) (-(n + 1)) ≫
      (postnikovLayerHomologyIso R C n).hom =
        (postnikovLayerHomologyIso R B n).hom ≫ homologyMap f.hom (-(n + 1)) := by
  have : QuasiIsoAt (C.X.πTruncGE (-(n + 1))) (-(n + 1)) :=
    CochainComplex.quasiIsoAt_πTruncGE _ _ _ le_rfl
  apply (cancel_mono (homologyMap (C.X.πTruncGE (-(n + 1))) (-(n + 1)))).1
  rw [Category.assoc, postnikovLayerHomologyIso_projection, ← homologyMap_comp,
    postnikovLayerMap_inclusion, homologyMap_comp]
  have ht := congrArg (fun g ↦ homologyMap g (-(n + 1)))
    (CochainComplex.πTruncGE_naturality f.hom (-(n + 1)))
  simp only [homologyMap_comp] at ht
  rw [Category.assoc, ← ht, ← Category.assoc, postnikovLayerHomologyIso_projection]
  rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
