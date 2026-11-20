module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneTruncation
public import SerrePositivity.HomologicalAlgebra.ComplexLimits.TruncationInclusionNaturality

/-!
# smart 切断の π/H 比較の元の複体射に対する自然性

DAG XIII §2.2 の零次数比較への前段。同じ延長同型・切断包含を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
variable {A : Type u} [CommRing A]

lemma smartTruncationHomologyIso_naturality {M N : Complex A} (f : M ⟶ N) (d : ℕ) :
    homologyMap (truncLE'Map f (ComplexShape.embeddingUpIntLE 0)) d ≫
      (smartTruncationHomologyIso A N d).hom =
    (smartTruncationHomologyIso A M d).hom ≫ homologyMap f (-(d : ℤ)) := by
  let e := ComplexShape.embeddingUpIntLE 0
  have hd : e.f d = -(d : ℤ) := by simp [e]
  have he : homologyMap (truncLE'Map f e) d ≫
      ((N.truncLE' e).extendHomologyIso e hd).inv =
      ((M.truncLE' e).extendHomologyIso e hd).inv ≫
        homologyMap (extendMap (truncLE'Map f e) e) (-(d : ℤ)) := by
    apply (cancel_epi ((M.truncLE' e).extendHomologyIso e hd).hom).mp
    simp only [Iso.hom_inv_id_assoc,
      ← extendHomologyIso_hom_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  have ht : homologyMap (extendMap (truncLE'Map f e) e) (-(d : ℤ)) ≫
      homologyMap (N.truncLEIso e).inv (-(d : ℤ)) =
      homologyMap (M.truncLEIso e).inv (-(d : ℤ)) ≫
        homologyMap (truncLEMap f e) (-(d : ℤ)) := by
    simpa only [homologyMap_comp] using congrArg
      (fun k => homologyMap k (-(d : ℤ))) (_root_.SerrePositivity.EInfinity.ComplexLimits.truncLEIso_inv_naturality f e)
  have hi : homologyMap (truncLEMap f e) (-(d : ℤ)) ≫
      homologyMap (ιTruncLE N e) (-(d : ℤ)) =
      homologyMap (ιTruncLE M e) (-(d : ℤ)) ≫ homologyMap f (-(d : ℤ)) := by
    simpa only [homologyMap_comp] using congrArg
      (fun k => homologyMap k (-(d : ℤ))) (ιTruncLE_naturality f e)
  change homologyMap (truncLE'Map f e) d ≫
      ((N.truncLE' e).extendHomologyIso e hd).inv ≫
        homologyMap (N.truncLEIso e).inv (-(d : ℤ)) ≫
          homologyMap (ιTruncLE N e) (-(d : ℤ)) = _
  rw [← Category.assoc, he]
  simp only [Category.assoc]
  rw [← Category.assoc (homologyMap (extendMap (truncLE'Map f e) e) _), ht, Category.assoc, hi]
  rfl

end SerrePositivity.EInfinity.PowerOperation
