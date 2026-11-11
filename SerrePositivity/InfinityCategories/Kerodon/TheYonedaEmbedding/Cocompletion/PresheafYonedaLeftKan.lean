module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaReflectorLeftKan
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafNativeDensityKan
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition

/-!
概要：余完備な標的への全前層圏からの Yoneda 左 Kan 延長を構成する。
方針：各 Yoneda comma を小さい elements 図式へ戻し、その余極限を取る。
規約：標的の全小余極限を明示し、元の Yoneda と指定単位を保持する。
使われ方：余完備な Ind 模型の前層反映。

対応節は Kerodon 8.4（Tag 03V7）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion

variable {A : SSet.{u}} [Quasicategory A] {D : SSet.{u + 1}} [Quasicategory D]

/-- 概要：余完備な標的への Yoneda 局所図式は余極限を持つ。
方針：同じ小さい elements 比較で局所図式を制限する。
規約：全前層の任意の頂点を扱う。
使われ方：全前層圏からの左 Kan 延長の存在。 -/
lemma presheafYonedaLeftKanDiagram_hasColimit (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits D)
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ D)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A) F₀ v) := by
  obtain ⟨F, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv A).surjective v
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A) F₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F))
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasColimit_of_equivalentRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafElementsLeftKanComparison F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafElementsLeftKanComparison_isQCatEquivalence F)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafElementsLeftKanComparison_projection]
  exact hD _ _

/-- 概要：小余極限を持つ標的への全前層 Yoneda 左 Kan 延長が存在する。
方針：各小 elements 図式の余極限を元の存在定理へ渡す。
規約：全関手と指定単位の coherent な延長を得る。
使われ方：Ind 包含の左随伴候補。 -/
lemma presheaf_exists_yonedaLeftKan (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits D)
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ D) :
    ∃ (L : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A ⟶ D)
      (β : SSet.Homotopy F₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A ≫ L)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A) F₀ L β :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftExtension_of_local_colimits _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafYonedaLeftKanDiagram_hasColimit hD F₀)

variable {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ D}
  {L : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A ⟶ D}
  (β : SSet.Homotopy F₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A ≫ L))
  (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A) F₀ L β)

include β hβ

/-- 概要：Yoneda 左 Kan 延長の指定単位は可逆。
方針：元の Yoneda の充満忠実性を単位判定へ渡す。
規約：指定単位自体の可逆性。
使われ方：全密度余錐の像の計算。 -/
lemma presheafYonedaLeftKan_unit_isIso :
    IsIso (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftKanExtension_unit_isIso_of_fullyFaithful _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_isFullyFaithful A) β hβ

/-- 概要：Yoneda 左 Kan 延長の元の標準余錐は全て余極限。
方針：同じ可逆単位を指定変換付きの Kan 条件から消去する。
規約：元の候補関手の値を保持する。
使われ方：密度の elements 表示への制限。 -/
lemma presheafYonedaLeftKan_canonicalColimits (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A) L v) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanExtension_canonicalColimits_of_unit_isIso _ β hβ
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafYonedaLeftKan_unit_isIso β hβ) v

/-- 概要：全前層 Yoneda 左 Kan 延長は元の密度余錐を余極限へ送る。
方針：標準余錐を小さい elements 比較で制限し、全写像を照合する。
規約：元の前層と元の全余錐を保持する。
使われ方：前層反映の制限の回収。 -/
lemma presheafYonedaLeftKan_density_image_isColimit
    (F : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone L (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityCocone F)) := by
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A) L (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isColimitCone_iff_restrict_equivalentShape (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafElementsLeftKanComparison F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafElementsLeftKanComparison_isQCatEquivalence F) c).mp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafYonedaLeftKan_canonicalColimits β hβ _)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq (c.restrict _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone L (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityCocone F)) ?_).mp hc
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ (𝟙 _) ≫ (_ ≫ L) = _
  rw [← Category.assoc]
  exact congrArg (fun g ↦ g ≫ L) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafElementsLeftKanComparison_coconeMap F)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion
