module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceCylinderJointEndpoint
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoproductPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：coproduct 上の prism の垂直辺の可逆性。
方針：頂点の共同全射性と定値単体の自然性で比較する。
規約：時刻の標準区間は第一因子。
使われ方：指定した円柱の関手同型と厳密な持ち上げ。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：prism の垂直辺は形状の射による前合成と可換。
方針：射の定値一次単体に関する自然性を使う。
規約：零単体で指定した射の像そのものを扱う。
使われ方：貼った prism の垂直辺を各因子に還元する。 -/
lemma prismVertical_precomp {A B X : SSet.{u}} (i : A ⟶ B)
    (H : (Δ[1] : SSet.{u}) ⊗ B ⟶ X) (x : A _⦋0⦌) :
    H.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (i.app (Opposite.op ⦋0⦌) x) 1) =
    ((Δ[1] ◁ i) ≫ H).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) := by
  have h := ConcreteCategory.congr_hom
    (i.naturality (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op) x
  change i.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (i.app (Opposite.op ⦋0⦌) x) 1 at h
  change H.app _ (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _) =
    H.app _ (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), i.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))
  rw [h]
/-- 概要：各因子で垂直辺が可逆な prism を貼ると全体でも可逆。
方針：各頂点を二因子のいずれかから表示し、制限の式を使う。
規約：標的の quasicategory 性はこの判定に不要。
使われ方：指定自然変換と頂点固定のホモトピーの貼り合わせ。 -/
lemma coprodPrism_vertical_isInvertible {A B X : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X) (J : (Δ[1] : SSet.{u}) ⊗ B ⟶ X)
    (hH : ∀ x : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (H.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))))
    (hJ : ∀ x : B _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (J.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))))
    (x : (A ⨿ B) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coprodPrism H J).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))) := by
  obtain ⟨a, rfl⟩ | ⟨b, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sset_coprod_jointly_surjective A B (Opposite.op ⦋0⦌) x
  · rw [prismVertical_precomp (coprod.inl : A ⟶ A ⨿ B), _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coprodPrism_inl]
    exact hH a
  · rw [prismVertical_precomp (coprod.inr : B ⟶ A ⨿ B), _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coprodPrism_inr]
    exact hJ b

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
