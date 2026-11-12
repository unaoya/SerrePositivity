module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftStrictExistence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LeftCanonicalRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulBoundary

/-!
概要：局所余極限の存在の下で元の左 Kan 関手の制限は終対象上で自明 Kan fibration。
方針：単位の可逆性で厳密に延長し、既存の写像空間の充満忠実性と頂点全射性を合わせる。
規約：相対 join の図式ではなく既存の元の関手の全部分圏を用いる。
使われ方：左 Kan 拡張の coherent な選択の絶対的な制限定理。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：終対象上の単射による元の左 Kan 関手の制限は inner fibration。
方針：相対標的を通常の関手圏と表示し、全部分複体の包含と前合成を合成する。
規約：U の標的の終対象性を明示する。
使われ方：充満忠実性と厳密な存在を全境界充填へ合わせる。 -/
lemma kanRelativeLeftKanRestriction_terminal_innerFibration {K C D E : SSet.{u}}
    [Quasicategory D] (U : D ⟶ E) (hE : IsTerminal E) (δ : K ⟶ C) [Mono δ] :
    InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction U δ
      (Functor.PullbackObjObj.ofIsTerminal internalHom δ U hE)) := by
  have : InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanDiagrams U δ).ι :=
    inferInstanceAs (InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.KanRelativeLeftKanVertex U δ)).ι)
  change InnerFibration ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanDiagrams U δ).ι ≫ (pre δ).app D)
  exact ⟨innerFibrations.comp_mem _ _
    (InnerFibration.mem (q := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanDiagrams U δ).ι))
    (InnerFibration.mem (q := (pre δ).app D))⟩

/-- 概要：局所余極限が存在すれば元の左 Kan 関手の制限は終対象上で頂点全射。
方針：元の図式の厳密な延長を選び、標準相対条件を満たす全部分圏の頂点とする。
規約：自然同型による本質的全射性ではなく、実際の制限の等式を使う。
使われ方：元の関手圏からの制限の零次元境界の持ち上げ。 -/
lemma kanRelativeLeftKanRestriction_terminal_surjective {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) (hE : IsTerminal E) (δ : K ⟶ C) [Mono δ] [InnerFibration δ]
    (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful δ)
    (hcol : ∀ (F₀ : K ⟶ D) (c : C _⦋0⦌), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c)) :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction U δ
      (Functor.PullbackObjObj.ofIsTerminal internalHom δ U hE)).app (Opposite.op ⦋0⦌)) := by
  intro y
  obtain ⟨F₀, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K D).surjective y
  obtain ⟨G, hG, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftCanonical_strict_extension_of_local_colimits δ hδ F₀ (hcol F₀)
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.KanRelativeLeftKanVertex U δ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtendedFrom U δ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C D).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
    have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C D).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) = G :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C D).symm_apply_apply G
    rw [he]
    intro c
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_isColimit_of_terminal U hE _).2 (hc c)
  let x : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanDiagrams U δ : SSet.{u}) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G, by
    intro α
    have hα : α = 𝟙 _ := Subsingleton.elim _ _
    simpa only [hα, op_id, Functor.map_id_apply] using hv⟩
  refine ⟨x, ?_⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (δ ≫ G) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F₀
  rw [hG]

/-- 概要：局所余極限が存在すれば元の左 Kan 関手の制限は終対象上で自明 Kan fibration。
方針：指定 pinched 比較による充満忠実性、inner 性、厳密な頂点全射性を合わせる。
規約：δ は単射・inner・写像空間で充満忠実。
使われ方：絶対的な左 Kan 関手の coherent な選択と制限の可縮な fiber。 -/
lemma kanRelativeLeftKanRestriction_terminal_trivialKanFibration {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) (hE : IsTerminal E) (δ : K ⟶ C) [Mono δ] [InnerFibration δ]
    (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful δ)
    (hcol : ∀ (F₀ : K ⟶ D) (c : C _⦋0⦌), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction U δ
      (Functor.PullbackObjObj.ofIsTerminal internalHom δ U hE)) := by
  have := kanRelativeLeftKanRestriction_terminal_innerFibration U hE δ
  have : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanDiagrams U δ : SSet.{u}) :=
    inferInstanceAs (Quasicategory
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.KanRelativeLeftKanVertex U δ) : SSet.{u}))
  have : Quasicategory (Functor.PullbackObjObj.ofIsTerminal internalHom δ U hE).pt :=
    inferInstanceAs (Quasicategory ((ihom K).obj D))
  have hf := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeLeftKanRestriction_terminal_isFullyFaithful U hE δ
  exact hf.trivialKanFibration_of_surjective
    (kanRelativeLeftKanRestriction_terminal_surjective U hE δ hδ hcol)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
