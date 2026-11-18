module

public import SerrePositivity.InfinityCategories.Sheaves.MonoImageSieveCone
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.AsSmallRightConeTransport

/-!
概要：局所全射な単射の元の圏への制限に対し、層の係数の指定右 Kan 条件を証明する。
方針：元の像篩での指定降下を、既存の comma の局所輸送へ渡す。
規約：HTT 6.2.2.6 の篩での層条件に基づく。右 Kan 条件を追加仮定にしない。
使われ方：S8 の局所単射による切断の不変性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u}
variable {E : SSet.{u + 1}} [Quasicategory E]

/-- 元の恒等余単位の全局所錐が極限であることを、同じ指定右 Kan 条件にまとめる。 -/
lemma monoLocal_isRightKanExtension (J : GrothendieckTopology C)
    (φ : P ⟶ Q) [Mono φ] [CategoryTheory.Presheaf.IsLocallySurjective J φ]
    (O : Presheaf C E) (hO : IsSheaf J O) :
    IsRightKanExtension (nerveMap (asSmallLocalFunctor φ.mapElements))
      (nerveMap (asSmallLocalFunctor (Functor.Elements.π P)) ≫ (nerveAsSmallIso Cᵒᵖ).inv ≫ O)
      (nerveMap (asSmallLocalFunctor (Functor.Elements.π Q)) ≫ (nerveAsSmallIso Cᵒᵖ).inv ≫ O)
      (kanRightCounitPostcomp
        (δ := nerveMap (asSmallLocalFunctor φ.mapElements))
        (F := nerveMap (asSmallLocalFunctor (Functor.Elements.π Q)))
        (F₀ := nerveMap (asSmallLocalFunctor (Functor.Elements.π P)))
        (nerveNatTransHomotopy (asSmallRightCounit φ.mapElements φ.mapElementsCompπIso.hom))
        ((nerveAsSmallIso Cᵒᵖ).inv ≫ O)) := by
  intro v
  obtain ⟨q, rfl⟩ := (nerveEquiv (C := AsSmall.{u + 1} Q.Elements)).symm.surjective v
  let j : Q.Elements := AsSmall.down.obj q
  have hq : AsSmall.up.obj j = q := by cases q; rfl
  rw [← hq]
  refine ⟨nerveRightConeTransportPostcomp (asSmallLocalFunctor φ.mapElements)
    (asSmallRightCounit φ.mapElements φ.mapElementsCompπIso.hom)
      (AsSmall.up.obj j) ((nerveAsSmallIso Cᵒᵖ).inv ≫ O), ?_⟩
  exact (asSmallRightConeTransportPostcomp_isLimit_iff φ.mapElements
    φ.mapElementsCompπIso.hom j O).mpr (imageSieveCommaRestrictionCone_isLimit J φ j O hO)

end SerrePositivity.InfinityCategories.Sheaves
