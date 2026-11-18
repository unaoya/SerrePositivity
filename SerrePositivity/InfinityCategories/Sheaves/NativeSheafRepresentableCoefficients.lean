module

public import SerrePositivity.InfinityCategories.Sheaves.NativeSheafUniverseLift
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RepresentableLimitCharacterization

/-!
概要：元のnativeな層の同じ被覆錐を、共変表現可能な空間値の層へ送る。
方針：同じ錐の宇宙移送と、既存の共変表現可能関手の極限保存を組み合わせる。
規約：HTT 5.1.3.2・6.2.2.6、Kerodon §8.3（Tag 03LZ）の既存構成の係数移送の法則。
  係数のpresentable性や新しい極限の存在を課さず、元の全被覆錐を使う。
使われ方：S8 の任意の係数から空間値へ移す際の入力。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u}} [Quasicategory E]

/-- 元の各被覆篩の同じ極限錐は、共変表現可能な空間値の層条件を与える。 -/
lemma NativeIsSheaf.covariantRepresentable {J : GrothendieckTopology C}
    {F : nerve Cᵒᵖ ⟶ E} (hF : NativeIsSheaf J F) (x : E _⦋0⦌) :
    IsSheaf J ((SSet.uliftFunctor.{u + 1, u}).map F ≫ covariantRepresentableInfinity x) := by
  intro U S hS
  let G := covariantRepresentableInfinity x
  have h := covariantRepresentableInfinity_isLimit (nativeRestrictionCone F S) (hF U S hS) x
  have hv : (mapJoinCone G (JoinCone.ulift.{u, u + 1} (nativeRestrictionCone F S))).val =
      (restrictionCone ((SSet.uliftFunctor.{u + 1, u}).map F ≫ G) S).val := by
    change (JoinCone.ulift.{u, u + 1} (nativeRestrictionCone F S)).val ≫ G = _
    rw [nativeRestrictionCone_ulift_val]
    rfl
  exact (isLimitCone_iff_of_cone_val_eq _ _ hv).mp h

end SerrePositivity.InfinityCategories.Sheaves
