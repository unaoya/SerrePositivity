module

public import SerrePositivity.InfinityCategories.Sheaves.PresheafYonedaShapeIso
public import SerrePositivity.InfinityCategories.Sheaves.NativeWeightedSections
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanShapeIsoTransport

/-!
概要：固定した元の反対 Yoneda に沿って、全重みの同じ右 Kan 延長を構成する。
方針：実際の Yoneda の右 Kan 延長の存在を、指定した形状同型と関手同型で移す。
  文献対応：HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）、S8 の重み付き切断。
規約：元の oppositeSpaceYoneda を用い、一つの全関手と指定変換を結論にする。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 固定した元の反対 Yoneda に沿う、全重み上の一つの右 Kan 延長の存在。
HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）。形状・係数移送の合成則。 -/
lemma exists_weightedSections (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    ∃ (G : (PresheafCat C SpaceInfinity.{u}).op ⟶ E)
      (ε : SSet.Homotopy (oppositeSpaceYoneda C ≫ G) O),
      IsRightKanExtension (oppositeSpaceYoneda C) O G ε := by
  apply (exists_weightedSections_iff_nativeShape C O).mpr
  have h := (exists_rightKanExtension_iff_of_isoSquare
    (fixedYonedaDomainIso C) (SSet.opFunctor.mapIso (fixedPresheafShapeIso C)).symm
    (nativeSetShapeOppositeYoneda_square C) ((fixedYonedaDomainIso C).inv ≫ O)).mpr
      (exists_nativeWeightedSections hE ((fixedYonedaDomainIso C).inv ≫ O))
  have he : (fixedYonedaDomainIso C).hom ≫ ((fixedYonedaDomainIso C).inv ≫ O) = O := by
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [he] at h
  exact h

end SerrePositivity.InfinityCategories.Sheaves
