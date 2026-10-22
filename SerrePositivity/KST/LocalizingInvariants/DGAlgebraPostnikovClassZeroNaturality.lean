module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroClassMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassNaturality

/-!
概要：元の class 標的射と零底への射が、同じ dg 代数射に沿って厳密に可換になる。
方針：底射と係数射の実対角直和を比較し、Postnikov 遷移の自然性を使う。
規約：零底後の全 class 射を保つ。使われ方：指定右中央経路と貼合せの同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n)

lemma postnikovClassToZeroBase_naturality : postnikovDerivationTargetMap R f n hn ≫
    postnikovClassToZeroBase R C n hn 1 =
      postnikovClassToZeroBase R B n hn 1 ≫ postnikovZeroClassMap R n 1 f := by
  apply Mon.Hom.ext
  simp only [Mon.comp_hom', postnikovDerivationTargetMap_hom, postnikovClassToZeroBase_hom,
    postnikovZeroClassMap_hom, cochainBiprodMap_comp]
  have h := congrArg Mon.Hom.hom (postnikovTransition_naturality R B f n 0 hn)
  simpa only [Mon.comp_hom', Category.id_comp, Category.comp_id] using
    congrArg (fun k => biprod.map k ((postnikovLayerMap R f n)⟦(1 : ℤ)⟧')) h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
