module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationProjectionNaturality
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaNormalizationProjections
/-! # 前後の標準合成面の replacement 射影一致

概要：前正規化後の終側面と、元 Hom からの終標準面が同じ三角形を与える。
方針：前正規化の replacement 射影が元鎖射影に厳密一致することを、coherent 三角形へ移す。
規約：辺だけでなく三角形全体を比較し、Small 仮定を追加しない。
使われ方：augmentation 四面体の残る単位面を高次貼り合わせで消去する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type (max u v)) [DGCategory R E]
  (X Y : DGFunctorCommaObject R E E (DGFunctor.id E))
  {K : SSet.{max u v}} (f : K ⟶ DGNerve.pinchedHom R
    (DGFunctorCommaObject R E E (DGFunctor.id E)) X Y)
local notation "Q" => DGFunctorCommaObject R E E (DGFunctor.id E)
lemma dgGluingPreNormalizeReplacementInput_eq :
    ((f ≫ pinchedHomChainMap (D := Q) (E := Q)
      (dgGluingIdentityCommaPreNormalizeHom R E X Y)) ≫
        pinchedHomChainMap ((dgFunctorCommaReplacement R E E (DGFunctor.id E)).map
          (dgGluingIdentityCommaObject R E X.replacement) Y)) =
      f ≫ pinchedHomChainMap ((dgFunctorCommaReplacement R E E (DGFunctor.id E)).map X Y) := by
  have hc := pinchedHomChainMap_comp (D := Q) (E := Q) (T := E)
    (x := X) (y := Y) (x' := dgGluingIdentityCommaObject R E X.replacement) (y' := Y)
    (x'' := X.replacement) (y'' := Y.replacement)
    (dgGluingIdentityCommaPreNormalizeHom R E X Y)
    ((dgFunctorCommaReplacement R E E (DGFunctor.id E)).map
      (dgGluingIdentityCommaObject R E X.replacement) Y)
  rw [Category.assoc, ← hc]
  change f ≫ pinchedHomChainMap (D := Q) (E := E)
    (dgGluingIdentityCommaPreNormalizeHom R E X Y ≫
      dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E) _ _) = _
  rw [dgGluingIdentityCommaPreNormalizeHom_replacement R E X Y]
  rfl
lemma dgGluingPostExitTriangle_replacement_eq :
    dgGluingSlicePrismTriangle (dgGluingIdentityCommaPostNormalizePrism R E X Y f) ≫
      dgNerve.map (dgFunctorCommaReplacement R E E (DGFunctor.id E)) =
    dgGluingNormalizationExitTriangle R E X Y f ≫
      dgNerve.map (dgFunctorCommaReplacement R E E (DGFunctor.id E)) := by
  have hp := dgGluingPostNormalizeProjectionInput_naturality R E X Y f
    (dgFunctorCommaReplacement R E E (DGFunctor.id E))
  have he := dgGluingExitProjectionInput_naturality R E X Y f
    (dgFunctorCommaReplacement R E E (DGFunctor.id E))
  dsimp only [DGGluingPostNormalizeProjectionInput] at hp
  dsimp only [DGGluingExitProjectionInput] at he
  rw [dgGluingPreNormalizeReplacementInput_eq R E X Y f] at hp
  exact hp.trans he.symm
end SerrePositivity.InfinityCategories
