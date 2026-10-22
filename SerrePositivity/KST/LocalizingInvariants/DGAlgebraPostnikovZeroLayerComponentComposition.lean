module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroLayerComponents

/-!
概要：零底と層の実平方零代数射の成分抽出は、元の射の合成を保つ。
方針：元の対角表示と実直和の二包含・射影で合成を回収する。
規約：係数の作用を忘れた別の逆を選ばない。使われ方：実代数逆の四つの成分三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A B C : Mon (Complex R)}
  [A.X.IsStrictlyLE 0] [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (n : ℤ) (hn : 0 ≤ n)
  (r : postnikovZeroLayerAlgebra R A n ⟶ postnikovZeroLayerAlgebra R B n)
  (s : postnikovZeroLayerAlgebra R B n ⟶ postnikovZeroLayerAlgebra R C n)

include hn in
lemma postnikovZeroLayerHomBase_comp : postnikovZeroLayerHomBase R n (r ≫ s) =
    postnikovZeroLayerHomBase R n r ≫ postnikovZeroLayerHomBase R n s := by
  apply Mon.Hom.ext
  change biprod.inl ≫ (r.hom ≫ s.hom) ≫ biprod.fst =
    (postnikovZeroLayerHomBase R n r).hom ≫ (postnikovZeroLayerHomBase R n s).hom
  rw [postnikovZeroLayerHom_diagonal R n r hn, postnikovZeroLayerHom_diagonal R n s hn,
    cochainBiprodMap_comp, ← Category.assoc, biprod.inl_map]
  have hp : (biprod.inl : (postnikov R C 0).X ⟶
      (postnikov R C 0).X ⊞ postnikovLayer R C n) ≫ biprod.fst = 𝟙 _ := biprod.inl_fst
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => ((postnikovZeroLayerHomBase R n r).hom ≫
      (postnikovZeroLayerHomBase R n s).hom) ≫ t) hp).trans (Category.comp_id _))

include hn in
lemma postnikovZeroLayerHomCoefficient_comp :
    postnikovZeroLayerHomCoefficient R n (r ≫ s) =
      postnikovZeroLayerHomCoefficient R n r ≫ postnikovZeroLayerHomCoefficient R n s := by
  change biprod.inr ≫ (r.hom ≫ s.hom) ≫ biprod.snd =
    postnikovZeroLayerHomCoefficient R n r ≫ postnikovZeroLayerHomCoefficient R n s
  rw [postnikovZeroLayerHom_diagonal R n r hn, postnikovZeroLayerHom_diagonal R n s hn,
    cochainBiprodMap_comp, ← Category.assoc, biprod.inr_map]
  have hp : (biprod.inr : postnikovLayer R C n ⟶
      (postnikov R C 0).X ⊞ postnikovLayer R C n) ≫ biprod.snd = 𝟙 _ := biprod.inr_snd
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => (postnikovZeroLayerHomCoefficient R n r ≫
      postnikovZeroLayerHomCoefficient R n s) ≫ t) hp).trans (Category.comp_id _))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
