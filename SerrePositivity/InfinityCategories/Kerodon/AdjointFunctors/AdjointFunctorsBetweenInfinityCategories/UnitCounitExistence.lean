module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaInitialFromMapping
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaCounit

/-!
概要：各点の標準単位比較の同値条件から自然な余単位候補の存在を得る。
方針：comma の始対象性・始域射影の輸送・族の相対充填を順に適用する。
規約：輸送や全パラメータの写像空間同値を追加で仮定しない。三角恒等式は後続。
使われ方：Kerodon §6.2.6（Tag 02FQ） の指定単位による随伴の局所存在判定の逆方向。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：各点の標準単位比較の同値性から基底固定の comma 内の余単位比較が存在する。
方針：始対象性を相対充填へ移し、恒等矢印の族へ射を作る。
規約：ホモトピー全体の始域への射影を時間に定値に保つ。
使われ方：選んだ余単位候補と指定単位の整合性を追う比較データ。 -/
lemma UnitMappingSpaceCondition.exists_counitComparison
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} {η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)}
    (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition η) :
    ∃ H : SSet.Homotopy (G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSection η) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaIdentityFamily G),
      H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G = fst Y (Δ[1] : SSet.{u}) ≫ G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.exists_unitCommaCounitComparison_of_relativeInitial η
    hη.unitCommaInitialCondition.initialBoundaryLifting

/-- 概要：各点の標準単位比較の同値性から自然な余単位候補が存在する。
方針：comma 内の基底固定の比較を Y に射影する構成を使う。
規約：仮定は指定単位の各点の写像空間条件だけ。三角恒等式はまだ主張しない。
使われ方：局所存在判定で余単位を関手全体のホモトピーとして構成する段階。 -/
lemma UnitMappingSpaceCondition.exists_counitHomotopy
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} {η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)}
    (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition η) : Nonempty (SSet.Homotopy (G ≫ F) (𝟙 Y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.exists_unitCommaCounitHomotopy_of_relativeInitial η
    hη.unitCommaInitialCondition.initialBoundaryLifting

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
