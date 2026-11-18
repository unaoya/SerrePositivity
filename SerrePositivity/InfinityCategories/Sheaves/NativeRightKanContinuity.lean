module

public meta import SerrePositivity.Util.Citation

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.PresheafYonedaLeftKanColimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightOppositeCriterion
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoconeReversePostcomp
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalMap

/-!
概要：実際の反対 Yoneda の指定右 Kan 延長は、任意の小さい余極限を極限へ送る。
方針：既存の反転した指定変換を、二重反転の等式で元の左 Kan に戻し、全 Hom 比較の保存定理を使う。
  文献対応：HTT 5.1.5.6、Kerodon §8.4（Tag 03V7）、S8 の一般重みの切断。
規約：元の全関手・指定変換・全余錐を保持する。図式に sifted 性を仮定しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams
namespace SerrePositivity.InfinityCategories.Sheaves

private lemma leftKan_exists_of_shape_heq {K K' C C' D : SSet.{u}}
    (hK : K = K') (hC : C = C') {δ : K ⟶ C} {δ' : K' ⟶ C'} (hδ : HEq δ δ')
    {F₀ : K ⟶ D} {F : C ⟶ D} (β : SSet.Homotopy F₀ (δ ≫ F))
    (hβ : IsLeftKanExtension δ F₀ F β) :
    ∃ (F₀' : K' ⟶ D) (F' : C' ⟶ D) (β' : SSet.Homotopy F₀' (δ' ≫ F')),
      IsLeftKanExtension δ' F₀' F' β' ∧ HEq F F' := by
  cases hK
  cases hC
  have hd := eq_of_heq hδ
  subst δ'
  exact ⟨F₀, F, β, hβ, HEq.rfl⟩

private lemma oppositeMap_heq_of_source_eq {A B D : SSet.{u}} (h : A = B)
    {f : A ⟶ D} {g : B ⟶ D} (hf : HEq f g) : HEq (SSet.opFunctor.map f) (SSet.opFunctor.map g) := by
  cases h
  have hh := eq_of_heq hf
  cases hh
  rfl

/-- 実際の反対 Yoneda の指定右 Kan 延長は、任意の小さい元の余極限を極限へ送る。
HTT 5.1.5.6、Kerodon §8.4（Tag 03V7）。既存の大域的全 Hom 比較の保存定理を双対化する。 -/
@[cite HTT "5.1.5.6" (partial := special)
  "反対 Yoneda の指定右 Kan 延長による全小余極限の反転（双対）に特殊化する。全関手圏の同値はこの結論に含めない。"]
lemma nativeRightKan_map_colimit_isLimit {A : SSet.{u}} [Quasicategory A]
    {E : SSet.{u + 1}} [Quasicategory E]
    {O : ((SSet.uliftFunctor.{u + 1, u}).obj A).op ⟶ E}
    {G : (PresheafInfinity A).op ⟶ E}
    (α : SSet.Homotopy (SSet.opFunctor.map (yonedaInfinityMap A) ≫ G) O)
    (hα : IsRightKanExtension (SSet.opFunctor.map (yonedaInfinityMap A)) O G α)
    {I : SSet.{u}} {p : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ PresheafInfinity A}
    (c : JoinCocone p) (hc : IsColimitCone c) :
    IsLimitCone (mapJoinCone G (coconeReverseCone c)) := by
  have hd := kanIsRightKanExtension_opposite (SSet.opFunctor.map (yonedaInfinityMap A)) O G α hα
  obtain ⟨F₀, L, β, hβ, hL⟩ := leftKan_exists_of_shape_heq
    (opposite_opposite_eq ((SSet.uliftFunctor.{u + 1, u}).obj A))
    (opposite_opposite_eq (PresheafInfinity A))
    (opposite_map_map_heq (yonedaInfinityMap A))
    (rightKanOppositeTransformation (SSet.opFunctor.map (yonedaInfinityMap A)) O G α) hd
  have hLG : HEq (SSet.opFunctor.map L) G :=
    (oppositeMap_heq_of_source_eq (opposite_opposite_eq (PresheafInfinity A)) hL).symm.trans
      (opposite_map_map_heq G)
  have he : SSet.opFunctor.map L ≫ (SSet.opFunctorCompOpFunctorIso.app E).hom = G := by
    rw [opposite_doubleIso_eqToHom]
    have h := (conj_eqToHom_iff_heq (SSet.opFunctor.map L) G rfl (opposite_opposite_eq E)).mpr hLG
    have h' := congrArg (fun f => f ≫ eqToHom (opposite_opposite_eq E)) h
    simpa only [eqToHom_refl, Category.id_comp, Category.assoc, eqToHom_trans,
      eqToHom_refl, Category.comp_id] using h'
  have hcol := presheafYonedaLeftKan_map_isColimit β hβ c hc
  have hlim := (isLimitCone_reverse_postcomp_iff c L).mpr hcol
  have hpost := hlim.postcomp_of_isIso (SSet.opFunctorCompOpFunctorIso.app E).hom
  apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).mp hpost
  change ((coconeReverseCone c).val ≫ SSet.opFunctor.map L) ≫
      (SSet.opFunctorCompOpFunctorIso.app E).hom = (coconeReverseCone c).val ≫ G
  rw [Category.assoc, he]

end SerrePositivity.InfinityCategories.Sheaves
