module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.OctahedronForMorphisms
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.OctahedronModelTransport

/-! # 安定 ∞ 圏のホモトピー圏の三角構造

概要：安定 quasicategory のホモトピー圏は cofiber 列の像を distinguished とする三角圏である。
方針：既存の前三角構造に対し、二長方形の八面体模型を任意の入力へ同型輸送する。
規約：既存の前加法構造と整数シフトを用いる。使われ方：HA 1.1.2.14、長完全列と完全関手。
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：安定 quasicategory のホモトピー圏は八面体公理を満たす。
方針：任意の二射の八面体模型を用い、任意の三つの distinguished 三角形へ輸送する。
規約：distinguished 集合は cofiber 列の像。追加の有限極限や余極限の仮定は不要。
使われ方：構成済み Pretriangulated instance とともに h C の三角構造を公開する。 -/
instance isTriangulated_ho {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    IsTriangulated (hoFunctor.obj X) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isTriangulated_of_octahedronModels (fun f g => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.octahedronModel_of_morphisms f g)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.1.2.14" (partial := stronger-hyp) "仮定：安定準圏 X（Lean は IsStable を要求。HA の表現は点付き性・余ファイバー・懸垂同値）。結論：余ファイバー三角形と整数シフトを使う hX の三角圏構造（一致）。HA の形で仮定を与える入口は型にない。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isTriangulated_ho
attribute [cite HA "1.1.2.16"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isTriangulated_ho
attribute [cite HA "1.2.1.4" (partial := component) "仮定：安定準圏 C（HA と一致）。結論：hC に三角圏構造があるため、HA と同じ hC 上の TStructure を取れる。C 内の対応する充満 ∞ 部分圏を一緒に定める型は採用した宣言にない（Lean が弱い）。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isTriangulated_ho
attribute [cite HA "1.4.1.6" (partial := component) "仮定：前三角圏からアーベル圏への関手。反対圏に適用すれば反変（Lean が強い：一般の点付き準圏のホモトピー圏には前三角構造を仮定できない）。結論：三角を完全列に送る公理（Lean が弱い：集合値の次数族・suspension 同型と小余積を積にする公理を一組にした定義はない）。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isTriangulated_ho
