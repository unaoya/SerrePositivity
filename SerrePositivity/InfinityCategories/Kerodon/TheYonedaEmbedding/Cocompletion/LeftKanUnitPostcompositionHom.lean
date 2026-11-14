module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftKanHomMapPostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftTransportPostcomp
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHom

/-!
概要：同じ左 Kan 単位の後合成をホモトピー圏の射として照合する。
方針：同じ代表辺の端点輸送と既存の後合成則を使う。
規約：元のホモトピーを変更しない。使われ方：E01 の点評価した単位の普遍性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open Kerodon.LimitsAndColimits.KanExtensions
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion

/-- 概要：後合成して端点を揃えた単位の類は標準の後合成した単位の類。
方針：代表辺の一次単体は同じで、終端の結合則だけを輸送する。
規約：任意の単位を保持し、可逆性を仮定しない。
使われ方：Kerodon Tag 03M5・03W8、HTT 5.1.3.1・5.1.5.3 の
指定 Yoneda 比較の点評価で使う単位の計算法則。 -/
lemma kanLeftUnitPostcomp_hom {K C D E : SSet.{u}} {δ : K ⟶ C}
    {F₀ : K ⟶ D} {F : C ⟶ D} (β : SSet.Homotopy F₀ (δ ≫ F)) (q : D ⟶ E) :
    kanFunctorHomCongr rfl (Category.assoc δ F q)
      (postcomposeFunctorHom q
        (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β))) =
      Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (kanLeftUnitPostcomp β q)) := by
  have h := homMk_transport rfl (congrArg functorVertex (Category.assoc δ F q))
    (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp β q))
    (functorEdgeOfSimplicialHomotopy (kanLeftUnitPostcomp β q)) rfl
  simpa only [kanFunctorHomCongr, Iso.homCongr_apply, postcomposeFunctorHom_eq_map,
    functorHomotopyPostcomp_hom, eqToIso_refl, Iso.refl_inv, Iso.refl_hom,
    eqToHom_refl, Category.id_comp, Category.comp_id] using h

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion
