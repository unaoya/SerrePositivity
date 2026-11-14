module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ElementsDegreeFiber
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafBarObject
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.LeftKanShapeIso
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CofinalUniverseLift
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalCoconeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoconeValEquality

/-!
概要：同じ次数の離散全単体を、元の bar 左 Kan 添字へ cofinal に入れる。
方針：次数ファイバーの nerve 比較と元の局所添字の宇宙同型を合成する。
規約：元の次数と図式の全射影を保持する。
使われ方：各 bar 項を表現可能前層の小余積として読む。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

/-- 概要：同じ次数の離散ファイバーから、元の小さい左 Kan 添字への比較。
方針：ファイバーを通常の comma へ入れ、指定 nerve 同型を合成する。
規約：元の次数の小さい添字を固定する。
使われ方：全高次の right cofinal 性と図式の比較。 -/
def presheafBarDegreeComparison (n : ULiftHom.{u} (ULift.{u} SimplexCategoryᵒᵖ)) :
    nerve (Discrete ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarSimplexFamily F).obj n)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarDegree F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex n) :=
  nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsDegreeFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarSimplexFamily F) n) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarDegree F) n).hom

omit [Quasicategory C] in
/-- 概要：同じ離散次数ファイバーの比較は right cofinal。
方針：明示的な左随伴による cofinal 性と、元の nerve 同型を合成する。
規約：全単体を使い、非退化部分への制限は行わない。
使われ方：局所左 Kan 余極限の離散余積への縮約。 -/
lemma presheafBarDegreeComparison_isRightCofinal
    (n : ULiftHom.{u} (ULift.{u} SimplexCategoryᵒᵖ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (presheafBarDegreeComparison F n) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsDegreeFiber_nerve_isRightCofinal
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarSimplexFamily F) n).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_isIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarDegree F) n).hom)

/-- 概要：宇宙を合わせた同じ離散ファイバーから、元の bar 左 Kan 添字への比較。
方針：小さい比較の持ち上げに、元の局所添字の宇宙同型を合成する。
規約：指定次数の持ち上げを保持する。
使われ方：元の左 Kan 単位による各次数の余積余錐。 -/
def presheafBarDegreeUniverseComparison
    (n : ULiftHom.{u} (ULift.{u} SimplexCategoryᵒᵖ)) :
    (SSet.uliftFunctor.{u + 1, u}).obj
        (nerve (Discrete ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarSimplexFamily F).obj n))) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarDegree F)))
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex n)) :=
  (SSet.uliftFunctor.{u + 1, u}).map (presheafBarDegreeComparison F n) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.leftKanShapeUniverseIso (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarDegree F))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex n)).hom

omit [Quasicategory C] in
/-- 概要：元の bar 左 Kan 添字への宇宙比較も right cofinal。
方針：小さい比較の cofinal 性を持ち上げ、指定同型を合成する。
規約：余錐の頂点を別の模型へ移さない。
使われ方：指定された bar 項の小余積性。 -/
lemma presheafBarDegreeUniverseComparison_isRightCofinal
    (n : ULiftHom.{u} (ULift.{u} SimplexCategoryᵒᵖ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (presheafBarDegreeUniverseComparison F n) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift _ (presheafBarDegreeComparison_isRightCofinal F n)).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_isIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.leftKanShapeUniverseIso (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarDegree F))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex n)).hom)

omit [Quasicategory C] in
/-- 概要：元の宇宙比較は離散ファイバーからの同じ全射影を保つ。
方針：局所添字の宇宙同型と通常の comma の射影公式を合成する。
規約：元の指定次数の全単体を保持する。
使われ方：同じ余積図式の全写像の正規化。 -/
lemma presheafBarDegreeUniverseComparison_projection
    (n : ULiftHom.{u} (ULift.{u} SimplexCategoryᵒᵖ)) :
    presheafBarDegreeUniverseComparison F n ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarDegree F))) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex n)) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarFiberInclusion F n.objDown.down)) := by
  dsimp only [presheafBarDegreeUniverseComparison]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.leftKanShapeUniverseIso_projection,
    ← Functor.map_comp]
  apply congrArg (SSet.uliftFunctor.{u + 1, u}).map
  dsimp only [presheafBarDegreeComparison]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso_hom_projection]
  change nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsDegreeFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarSimplexFamily F) n ⋙
    CostructuredArrow.proj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarDegree F) n) = _
  apply congrArg nerveMap
  apply Discrete.functor_ext
  intro s
  rfl

/-- 概要：同じ次数の局所左 Kan 図式は、元の離散ファイバーの表現可能図式である。
方針：元の全射影の厳密な比較を入力図式へ後合成する。
規約：対象ごとの同値だけでなく図式の全射の等式を与える。
使われ方：各 bar 項の小余積余錐の始域の同定。 -/
lemma presheafBarDegreeUniverseComparison_diagram
    (n : ULiftHom.{u} (ULift.{u} SimplexCategoryᵒᵖ)) :
    presheafBarDegreeUniverseComparison F n ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarDegree F)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarInputDiagram F) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex n)) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarFiberInclusion F n.objDown.down)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarInputDiagram F := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram]
  rw [← Category.assoc, presheafBarDegreeUniverseComparison_projection]

/-- 概要：元の bar の各指定次数は、同じ離散表現可能図式の小余積となる。
方針：指定単位の局所余極限全余錐を、構成済みの cofinal 比較で制限する。
規約：bar 項の元の関手頂点を厳密な余錐頂点として保持する。
使われ方：任意前層の表現可能小余積による単体的表示。 -/
lemma presheafBarObject_degree_coproduct
    (n : ULiftHom.{u} (ULift.{u} SimplexCategoryᵒᵖ)) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarFiberInclusion F n.objDown.down)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarInputDiagram F),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ∧
        c.vertex = (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarObject F).app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex n)) := by
  obtain ⟨c, hc, hv⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarUnit_isLeftKanExtension F).colimitValue
    (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex n))
  have hr := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal
    (presheafBarDegreeUniverseComparison F n)
    (presheafBarDegreeUniverseComparison_isRightCofinal F n) c).mp hc
  have hdiag := presheafBarDegreeUniverseComparison_diagram F n
  let d := c.restrict (presheafBarDegreeUniverseComparison F n)
  let e : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarFiberInclusion F n.objDown.down)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarInputDiagram F) :=
    ⟨d.val, d.property.trans hdiag⟩
  exact ⟨e, (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq d e rfl).mp hr, hv⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.5.8.13"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarObject_degree_coproduct
