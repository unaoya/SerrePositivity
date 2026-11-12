module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.UnderSectionScaffold
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementConstant

/-!
概要：under 切断の大域 scaffold 評価は、元の積の両方の射影を厳密に保つ。
方針：切断族のパラメータ射影を一つの自然変換とし、同じ標準射列での評価と照合する。
規約：元の底を scaffold 評価後に選び直さず、係数の元の射影を使う。
使われ方：元の共同 left fibration と strict 図式の底上の大域比較。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Category.{u} I] {B E : SSet.{u}} (p : E ⟶ B ⊗ nerve I)

/-- 元のパラメータ射影を全添字で束ねた自然変換。 -/
def underSectionTotalProjection :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionTotalDiagram p ⟶ (CategoryTheory.Functor.const I).obj B where
  app := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFamilyProjection p
  naturality _ _ f := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFamilyMap p f ≫ _ = _ ≫ 𝟙 B
    rw [Category.comp_id, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFamilyMap_projection]

/-- replacement の元の係数の射影による、元の底への射。 -/
def underSectionScaffoldBase : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionTotalDiagram p) ⟶ B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementMap (underSectionTotalProjection p) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantIso I B).hom ≫ snd (nerve I) B

/-- 大域 scaffold 評価は元の底パラメータを厳密に保つ。 -/
lemma underSectionScaffold_fst :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionScaffold p ≫ p ≫ fst B (nerve I) = underSectionScaffoldBase p := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, τ⟩
  change (Δ[n] : SSet.{u}) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSections p (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.sectionFamilyProductBase B (nerveMap (Under.forget (σ.obj 0)))) at τ
  change (p ≫ fst B (nerve I)).app (Opposite.op ⦋n⦌)
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.universalScaffoldSimplex (p ≫ snd B (nerve I))
        ⟨σ, τ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsForget p (nerveMap (Under.forget (σ.obj 0)))⟩)) =
    SSet.yonedaEquiv (τ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFamilyProjection p (σ.obj 0))
  rw [← SSet.yonedaEquiv_comp]
  apply congrArg SSet.yonedaEquiv
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.universalScaffoldSimplex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_parameter]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsForget_uncurry_fst]
  simp only [Category.assoc, whiskerLeft_snd_assoc, lift_snd_assoc, Category.id_comp]
  rfl

/-- 同じ評価は、元の共同射影に重なる一つの底上の射。 -/
lemma underSectionScaffold_over_product :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionScaffold p ≫ p =
      lift (underSectionScaffoldBase p)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionTotalDiagram p)) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, underSectionScaffold_fst, lift_fst]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionScaffold_projection, lift_snd]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
