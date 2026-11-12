module
public import SerrePositivity.KST.Fibration.PointSourceFatDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinEndpointLifting

/-! # 可変終点の同じ矢印族を、両端を固定した coslice 図式へ移す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 元の全 fat join 図式と両端相対ホモトピーを持つ、通常の join 図式。 -/
structure PointSourceCosliceData {A X : SSet.{u}} (x : X _⦋0⦌) (g : A ⟶ X)
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) A ⟶ X) where
  cone : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) A ⟶ X
  left : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] A ≫ cone = yonedaEquiv.symm x
  right : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] A ≫ cone = g
  fatLeft : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] A ≫ F = yonedaEquiv.symm x
  fatRight : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr Δ[0] A ≫ F = g
  homotopy : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison Δ[0] A ≫ cone) F
  fixed : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion Δ[0] A ▷ (Δ[1] : SSet.{u})) ≫ homotopy.h =
    fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram (Δ[0] : SSet.{u}) A) Δ[1] ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion Δ[0] A ≫ F

/-- 始点と可変終点を変えず、同じ全矢印族の coslice 比較データを構成する。 -/
theorem exists_pointSourceCosliceData {A X : SSet.{u}} [Quasicategory X]
    (x : X _⦋0⦌) (g : A ⟶ X) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) A ⟶ X)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] A ≫ F = yonedaEquiv.symm x)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr Δ[0] A ≫ F = g) : Nonempty (PointSourceCosliceData x g F) := by
  obtain ⟨G, hG, H, hH, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.exists_joinDiagram_of_fatJoinDiagram
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion Δ[0] A ≫ F) F rfl
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] A ≫ G = yonedaEquiv.symm x := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    exact (congrArg (fun (m : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram (Δ[0] : SSet.{u}) A).obj d ⟶ X.obj d) =>
      m (Sum.inl z)) (NatTrans.congr_app hG d)).trans
        (ConcreteCategory.congr_hom (NatTrans.congr_app h₀ d) z)
  have hy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] A ≫ G = g := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    exact (congrArg (fun (m : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram (Δ[0] : SSet.{u}) A).obj d ⟶ X.obj d) =>
      m (Sum.inr z)) (NatTrans.congr_app hG d)).trans
        (ConcreteCategory.congr_hom (NatTrans.congr_app h₁ d) z)
  exact ⟨⟨G, hx, hy, h₀, h₁, H, hH⟩⟩

/-- 同じ通常の join 図式を、元の固定始点の coslice への実関手に読む。 -/
def PointSourceCosliceData.toCoslice {A X : SSet.{u}} {x : X _⦋0⦌} {g : A ⟶ X}
    {F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) A ⟶ X} (d : PointSourceCosliceData x g F) :
    A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (yonedaEquiv.symm x) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry d.cone d.left

/-- 同じ coslice 関手の射影は元の可変終点の図式と厳密に等しい。 -/
theorem PointSourceCosliceData.toCoslice_projection {A X : SSet.{u}}
    {x : X _⦋0⦌} {g : A ⟶ X} {F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) A ⟶ X}
    (d : PointSourceCosliceData x g F) :
    d.toCoslice ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (yonedaEquiv.symm x) = g :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderCurry_projection d.cone d.left).trans d.right

end SerrePositivity.KST.Fibration
