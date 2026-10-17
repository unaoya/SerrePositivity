module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleLeftRestrictionFamily
public import SerrePositivity.DifferentialGraded.Derived.RightKFlatComposition
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorLeftRestriction

/-! # 外側左制限比較の、元の前因子上での正規化計算 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (D : Type t) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D E)

/-- 固定K-flat後因子の左制限比較は、通常比較の局所化と既存制限表示で計算される。 -/
lemma derivedComposeWithLeftRestrictionIso_base_app
    (Q : RightKFlatBimoduleCategory A C E) (P : BimoduleCategory A B C) :
    (derivedComposeWithLeftRestrictionIso A B C E D F Q).hom.app
        ((bimoduleToDerived A B C).obj P) =
      (bimoduleToDerived A B D).map (composeLeftRestrictionIso A B C E D F P Q.obj).hom ≫
        (middleLeftRestrictionDerivedIso A B E D F).hom.app
          ((composeWith A B C E Q.obj).obj P) := by
  rw [derivedComposeWithLeftRestrictionIso_hom_app_calc]
  change 𝟙 _ ≫ _ ≫ _ ≫
      (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F).map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

end SerrePositivity.DifferentialGraded.BimoduleTensor
