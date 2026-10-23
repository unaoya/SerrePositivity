module

public import SerrePositivity.InfinityCategories.F2.CoconeTransformationEquivalence
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalDiagramRestriction

/-!
概要：native 余錐と定値図式への変換の比較は添字の制限に厳密に自然。
方針：両側を同じ図式・区間・パラメータの円柱に展開する。
規約：元の形状写像と固定頂点を保持する。使われ方：Kan の普遍性から全余錐の比較へ移る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 定値頂点を保つ、同じ元の図式間の全変換空間の制限。 -/
def constantTransformationRestriction {A K X : SSet.{u}}
    (i : A ⟶ K) (F : K ⟶ X) (z : X _⦋0⦌) :
    intervalMappingSpace (functorVertex F) (functorVertex (SSet.const z)) ⟶
      intervalMappingSpace (functorVertex (i ≫ F)) (functorVertex (SSet.const z)) :=
  intervalMappingPostOfEq ((pre i).app X) (functorVertex F) (functorVertex (SSet.const z))
    (functorVertex_precomposition i F)
    (by rw [functorVertex_precomposition, SSet.comp_const])

/-- 全変換の制限の円柱は、元の円柱の同じ添字への制限。 -/
lemma constantTransformationRestriction_prism {A K X T : SSet.{u}}
    (i : A ⟶ K) (F : K ⟶ X) (z : X _⦋0⦌)
    (a : T ⟶ intervalMappingSpace (functorVertex F) (functorVertex (SSet.const z))) :
    F2.constantTransformationPrism (a ≫ constantTransformationRestriction i F z) =
      (i ▷ (Δ[1] : SSet.{u}) ▷ T) ≫ F2.constantTransformationPrism a := by
  rw [F2.constantTransformationPrism, constantTransformationRestriction,
    intervalMappingPostOfEq_uncurry, uncurry_pre_app, ← Category.assoc,
    ← associator_naturality_left, Category.assoc]
  rfl

/-- native 余錐の同じ制限の円柱も、元の円柱の添字制限そのもの。 -/
lemma coconeParameterPrism_restrict {A K X T : SSet.{u}}
    (i : A ⟶ K) (F : K ⟶ X) (z : X _⦋0⦌) (a : T ⟶ coconeMappingSpace F z) :
    F2.coconeParameterPrism (a ≫ cosliceRestrictionFiberMap F i z) =
      (i ▷ (Δ[1] : SSet.{u}) ▷ T) ≫ F2.coconeParameterPrism a := by
  rw [F2.coconeParameterPrism, coconeMappingSpace_restrict_uncurry, ← Category.assoc]
  have h := joinCylinderMap_naturality i (𝟙 T)
  simpa only [fatJoinCylinderMap, tensorHom_id, Category.assoc,
    F2.coconeParameterPrism] using
      congrArg (fun q => q ≫ sliceUnderUncurry
        (a ≫ vertexFiberι (sliceUnderProjection F) z)) h.symm

/-- 余錐から全変換への元の比較は、任意の添字写像に厳密に自然。 -/
lemma coconeTransformationMap_restrict {A K X : SSet.{u}}
    (i : A ⟶ K) (F : K ⟶ X) (z : X _⦋0⦌) :
    cosliceRestrictionFiberMap F i z ≫ F2.coconeTransformationMap (i ≫ F) z =
      F2.coconeTransformationMap F z ≫ constantTransformationRestriction i F z := by
  apply F2.constantTransformationPrism_injective
  rw [F2.coconeTransformationMap_prism, constantTransformationRestriction_prism]
  have h := coconeParameterPrism_restrict i F z (𝟙 (coconeMappingSpace F z))
  have he := F2.coconeTransformationMap_prism (𝟙 (coconeMappingSpace F z))
  simp only [Category.id_comp] at h he
  rw [he]
  exact h

end SerrePositivity.InfinityCategories.F2.Ind
