module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftConstantFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftUnitCanonical

/-!
概要：指定左 Kan 変換とその局所余錐の輸送を標的の射で後合成する。
方針：元の円柱に同じ射を後合成し、結合則だけで標準の端点の表示を揃える。
規約：変換や局所輸送の代表を選び直さない。
使われ方：一般の U 上で単位の像の可逆性から局所の絶対余極限を回収する。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：指定単位を後合成し、終端の結合順序を標準の表示へ揃える。
方針：後合成したホモトピーと同じ raw な円柱を使う。
規約：終端は δ≫(F≫U) とする。
使われ方：U 上の局所輸送の入力となる指定変換。 -/
def kanLeftUnitPostcomp {K C D E : SSet.{u}} {δ : K ⟶ C}
    {F₀ : K ⟶ D} {F : C ⟶ D} (β : SSet.Homotopy F₀ (δ ≫ F)) (U : D ⟶ E) :
    SSet.Homotopy (F₀ ≫ U) (δ ≫ (F ≫ U)) where
  h := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp β U).h
  h₀ := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp β U).h₀
  h₁ := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp β U).h₁.trans (Category.assoc δ F U)
  rel := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp β U).rel

/-- 概要：局所余錐の輸送を U で写すと後合成した指定単位の局所輸送になる。
方針：円柱全体に後合成し、標準余錐の後合成の式で終端を照合する。
規約：元の輸送 t をそのまま写す。
使われ方：単位の U 像が可逆なとき像の余錐の余極限性を判定する。 -/
def kanLeftTransportPostcomp {K C D E : SSet.{u}} {δ : K ⟶ C}
    {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)} {c : C _⦋0⦌}
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport δ F₀ F β c) (U : D ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport δ (F₀ ≫ U) (F ≫ U) (kanLeftUnitPostcomp β U) c where
  family := t.family ≫ U
  finish := by
    rw [← Category.assoc, t.finish, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonicalCocone_postcomp_val]
  diagram := by
    rw [← Category.assoc, t.diagram]
    simp only [Category.assoc]
    rfl
  fixedVertex := by
    rw [← Category.assoc, t.fixedVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonicalCocone_postcomp_val]
    simp only [Category.assoc]

/-- 概要：後合成した局所輸送の余錐の値は元の余錐の値の後合成。
方針：時刻零への制限と後合成の結合順序を計算する。
規約：図式の表示は異なっても、余錐全体の射は厳密に一致する。
使われ方：U による像の余極限条件を元の相対余極限と合わせる。 -/
lemma kanLeftTransportPostcomp_cocone_val {K C D E : SSet.{u}} {δ : K ⟶ C}
    {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)} {c : C _⦋0⦌}
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport δ F₀ F β c) (U : D ⟶ E) :
    (kanLeftTransportPostcomp t U).cocone.val = t.cocone.val ≫ U :=
  (Category.assoc _ _ _).symm

/-- 概要：指定単位の U による像が可逆なら標準の後合成した単位も可逆。
方針：h Fun の後合成の公式と、同じ raw な辺による可逆性の不変性を使う。
規約：h Fun の指定射の像そのものの可逆性を仮定する。
使われ方：像の局所輸送を全体の同型にする。 -/
lemma kanLeftUnitPostcomp_isIso {K C D E : SSet.{u}} {δ : K ⟶ C}
    {F₀ : K ⟶ D} {F : C ⟶ D} (β : SSet.Homotopy F₀ (δ ≫ F)) (U : D ⟶ E)
    (hU : IsIso ((hoFunctor.map ((ihom K).map U)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β)))) :
    IsIso (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (kanLeftUnitPostcomp β U))) := by
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp β U)) := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp β U)))
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom]
    exact hU
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (f :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (kanLeftUnitPostcomp β U)) rfl).1 hi

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
