module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsRestriction

/-!
概要：切断錐の制限の射影は、ホモトピー圏の任意の射に自然である。
方針：既存の制限関手と頂点射影の等式を、通常の自然変換の自然性で評価する。
規約：HTT §1.2.13、Kerodon §7.1（Tag 02H1）の既存構成の射影の法則。
使われ方：S8 の重みの射では、制限錐の極限性を仮定せずに比較射を制限する。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight
variable {C : Type u} [SmallCategory C] {X : SSet.{u + 1}} [Quasicategory X]
  {P Q : C ⥤ Type u}

/-- 任意の切断錐の射は、同じ頂点等式を介して制限前後で同じ射を持つ。 -/
lemma restrictSectionsFunctor_projection_naturality (φ : P ⟶ Q)
    (O : (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶ X) (c d : JoinCone (diagram Q O))
    (ℓ : (HomotopyCategory.mk c : hoFunctor.obj (sliceOver (diagram Q O))) ⟶
      HomotopyCategory.mk d) :
    (hoFunctor.map (sliceOverProjection (diagram P O))).toFunctor.map
      ((hoFunctor.map (restrictSectionsFunctor φ O)).toFunctor.map ℓ) ≫
        eqToHom (congrArg HomotopyCategory.mk
          (congrArg (fun f => f.app (Opposite.op ⦋0⦌) d)
            (restrictSectionsFunctor_projection φ O))) =
      eqToHom (congrArg HomotopyCategory.mk
        (congrArg (fun f => f.app (Opposite.op ⦋0⦌) c)
          (restrictSectionsFunctor_projection φ O))) ≫
        (hoFunctor.map (sliceOverProjection (diagram Q O))).toFunctor.map ℓ := by
  have hp : (hoFunctor.map (restrictSectionsFunctor φ O)).toFunctor ⋙
      (hoFunctor.map (sliceOverProjection (diagram P O))).toFunctor =
        (hoFunctor.map (sliceOverProjection (diagram Q O))).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp,
      restrictSectionsFunctor_projection]
  have h := (eqToHom hp).naturality ℓ
  simp only [eqToHom_app] at h
  exact h

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight
