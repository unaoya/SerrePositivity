module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpecifiedConeTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：指定 prism に沿う極限錐の輸送を追跡可能なデータとして保持する。
方針：頂点・全錐のホモトピー・二因子への厳密な制限を一つにまとめる。
規約：極限性は証明済みの存在定理から構成する。
使われ方：Cat_∞ の引き戻し錐の二脚と元の射影の比較。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：指定した可逆 prism に沿う極限錐の輸送とその制限の証拠。
方針：構成した錐と全錐の可逆ホモトピーを保持する。
規約：頂点と図式上のホモトピーを厳密に指定する。
使われ方：輸送後の錐の二脚を具体的に追跡する。 -/
structure SpecifiedLimitConeTransport {K X : SSet.{u}} {p q : K ⟶ X}
    (H : (Δ[1] : SSet.{u}) ⊗ K ⟶ X) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q) where
  /-- 元の図式上の輸送後の錐。 -/
  cone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p
  /-- 輸送後の錐の極限性。 -/
  isLimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone cone
  /-- 頂点の厳密な一致。 -/
  vertex_eq : cone.vertex = d.vertex
  /-- 全錐の指定した方向のホモトピー。 -/
  homotopy : SSet.Homotopy cone.val d.val
  /-- 頂点と元の図式への全時刻の厳密な制限。 -/
  boundary :
    (coprod.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K) ▷ (Δ[1] : SSet.{u})) ≫ homotopy.h =
      (β_ ((Δ[0] : SSet.{u}) ⨿ K) (Δ[1] : SSet.{u})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneBoundaryPrism d H
  /-- 全頂点でのホモトピーの可逆性。 -/
  vertical_isInvertible :
    ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge homotopy x).toTruncated

/-- 概要：指定した可逆 prism から追跡可能な極限錐の輸送を構成する。
方針：指定 prism の延長定理の錐とホモトピーを同時に選ぶ。
規約：頂点と指定自然変換の一致を構成のデータに含める。
使われ方：元の cospan の引き戻し錐の選択。 -/
def specifiedLimitConeTransport {K X : SSet.{u}} [Quasicategory X] {p q : K ⟶ X}
    (H : (Δ[1] : SSet.{u}) ⊗ K ⟶ X)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ H = p) (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ H = q)
    (hH : ∀ x : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (H.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))))
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d) : SpecifiedLimitConeTransport (p := p) H d := by
  let h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.exists_limitCone_of_specifiedPrism H h₀ h₁ hH d hd
  let c := Classical.choose h
  have hc := Classical.choose_spec h
  let G := Classical.choose hc.2.2
  have hG := Classical.choose_spec hc.2.2
  exact ⟨c, hc.1, hc.2.1, G, hG.1, hG.2⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
