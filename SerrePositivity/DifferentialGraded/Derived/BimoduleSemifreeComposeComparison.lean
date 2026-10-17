module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleComposeHomotopy
public import SerrePositivity.DifferentialGraded.Derived.BimoduleSemifreeComparison

/-! # semifree解像度の比較増大squareを任意の前因子と合成した後の整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleSemifreeResolution
open CategoryTheory BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]

/-- semifree比較の増大squareは、任意の前因子との合成後の導来圏でも可換。 -/
lemma composeAfter_comparison_fac (P : BimoduleCategory A B D) {Q : BimoduleCategory A D E}
    (R S : BimoduleSemifreeResolution A D E Q) :
    (bimoduleToDerived A B E).map ((composeAfter A B D E P).map (R.comparison S)) ≫
        (bimoduleToDerived A B E).map ((composeAfter A B D E P).map S.π) =
      (bimoduleToDerived A B E).map ((composeAfter A B D E P).map R.π) := by
  let J := rightModuleBimoduleEquivalence A D E
  let T := composeAfter A B D E P ⋙ bimoduleToDerived A B E
  have h := composeAfter_map_eq_of_source_homotopy A B D E P
    (R.toProjectiveResolution.comparison S.toProjectiveResolution ≫ S.toProjectiveResolution.π)
    R.toProjectiveResolution.π
    (((moduleToHomotopy A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ).map_comp _ _).trans
      (R.toProjectiveResolution.comparison_fac S.toProjectiveResolution))
  change T.map (J.functor.map (_ ≫ _)) = T.map (J.functor.map _) at h
  rw [J.functor.map_comp, T.map_comp] at h
  have hh := congrArg (fun k => k ≫ T.map (J.counitIso.app Q).hom) h
  have haug (U : BimoduleSemifreeResolution A D E Q) :
      T.map (J.functor.map U.toProjectiveResolution.π) ≫ T.map (J.counitIso.app Q).hom =
        T.map U.π :=
    (T.map_comp _ _).symm.trans (congrArg T.map U.augmentation_fac)
  rw [Category.assoc, haug S, haug R] at hh
  exact hh

end SerrePositivity.DifferentialGraded.BimoduleSemifreeResolution
