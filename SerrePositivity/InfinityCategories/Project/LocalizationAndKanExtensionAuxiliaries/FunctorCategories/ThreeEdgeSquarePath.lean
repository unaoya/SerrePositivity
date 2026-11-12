module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.ThreeEdgeSquareBoundary
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.RelativeHomotopyInvertible
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFamilyPath

/-!
概要：三辺固定の正方形比較を、同じ境界経路を持つ可逆 path にする。
方針：三辺が全頂点を含むことから点ごとの可逆性を示し、元の射を保って持ち上げる。
規約：全体図式の path と右辺の path の選択を共有する。
使われ方：B1 の順方向比較と復元側の指定境界輸送の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

section
variable {A X : SSet.{u}} [Quasicategory X] {U V W : A ⟶ X}
variable {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
variable {d₀ d₁ : SSet.Homotopy U W} {T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₀}
variable {Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare l r d₁} (c : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.ThreeEdgeSquareComparison T Q)

/-- 概要：三辺固定の正方形比較の各頂点の時間辺は可逆。
方針：三辺が全頂点を含み、相対条件が各時間辺を恒等辺にすることを使う。
規約：指定した全体ホモトピーそのものについての可逆性。
使われ方：同じホモトピーからの可逆 path への持ち上げ。 -/
lemma ThreeEdgeSquareComparison.pointwise_isInvertible :
    ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge c.homotopy v).toTruncated :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.relativeHomotopy_pointwise_isInvertible _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges.ι _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges_vertex_surjective
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges.ι ≫ Q.diagram) c.homotopy c.restriction

/-- 概要：正方形全体の比較を元の射を保って可逆 path にする。
方針：点ごとの可逆性により全部分複体へ持ち上げる。
規約：関手同型からの代表の再選択をしない。
使われ方：復元側の可逆 path による境界輸送との比較。 -/
noncomputable def ThreeEdgeSquareComparison.path :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath ((ihom A).obj X) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.pointwiseHomotopyPath c.homotopy c.pointwise_isInvertible

/-- 概要：可逆 path の包含後の図式は元の全体ホモトピーの curry。
方針：持ち上げの仕様を使う。
規約：図式の厳密な一致。
使われ方：境界 path の等式の確認。 -/
lemma ThreeEdgeSquareComparison.path_ι : c.path ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι ((ihom A).obj X) =
    curry ((β_ (Δ[1] : SSet.{u}) ((Δ[1] : SSet.{u}) ⊗ Δ[1])).hom ≫ c.homotopy.h) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.pointwiseHomotopyPath_ι _ _

/-- 概要：全体 path は指定三角形から補完した正方形から始まる。
方針：元のホモトピーの始点を厳密に回収する。
規約：始点の同型ではなく射の一致。
使われ方：指定始点を持つ輸送との比較。 -/
lemma ThreeEdgeSquareComparison.path_zero :
    c.path ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0 = (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorSquareOfCompositionTriangle T).diagram :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.pointwiseHomotopyPath_zero _ _

/-- 概要：全体 path は元の正方形で終わる。
方針：元のホモトピーの終点を厳密に回収する。
規約：終点の同型ではなく射の一致。
使われ方：元の comma 正方形の回収。 -/
lemma ThreeEdgeSquareComparison.path_one : c.path ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 1 = Q.diagram :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.pointwiseHomotopyPath_one _ _

/-- 概要：全体の可逆 path は三辺部分図式上で定値となる。
方針：元のホモトピーの相対条件を可逆 path の固定条件へ移す。
規約：三辺上の path 全体を固定する。
使われ方：復元側と同じ境界 path を持つ全体輸送の構成。 -/
lemma ThreeEdgeSquareComparison.path_restriction :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges.ι ≫ c.path =
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges.ι ≫ Q.diagram) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl ((ihom A).obj X) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.pointwiseHomotopyPath_restriction _ _ _ _ c.restriction

end

section
variable {A X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌} {V : A ⟶ X}
variable {l : SSet.Homotopy (SSet.const x) V} {r : SSet.Homotopy V (SSet.const y)}
variable {d₀ d₁ : SSet.Homotopy (SSet.const x : A ⟶ X) (SSet.const y)}
variable {T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₀} {Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare l r d₁}
variable (c : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.ThreeEdgeSquareComparison T Q) (f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y)
variable (hf : curry d₀.h = curry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).h)
variable (hg : curry d₁.h = curry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy g).h)

/-- 概要：正方形全体の可逆 path の右辺は、取り出した族のホモトピーの path そのもの。
方針：包含後に検査し、正方形の回収と時間交換の自然性を使う。
規約：独立な path の選択でなく、実際の可逆 path の厳密な一致。
使われ方：順方向比較と復元側の指定境界 path を一致させる。 -/
lemma ThreeEdgeSquareComparison.path_right :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ c.path = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyPath (c.familyHomotopy f g hf hg) := by
  have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι ((ihom A).obj X)) := by
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι
    infer_instance
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι ((ihom A).obj X))).mp
  rw [Category.assoc, c.path_ι,
    show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyPath (c.familyHomotopy f g hf hg) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι ((ihom A).obj X) =
      curry ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilySquare (c.familyHomotopy f g hf hg))
      from _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _]
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry, uncurry_curry, c.familyHomotopy_square]
  have hs : (Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫
      (β_ (Δ[1] : SSet.{u}) ((Δ[1] : SSet.{u}) ⊗ Δ[1])).hom =
        (β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rw [← Category.assoc, hs, Category.assoc]
  rfl

end

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
