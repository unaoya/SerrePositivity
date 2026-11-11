module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialFiberMapTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeMappingPiZero
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CosliceTriangleFiber

/-!
概要：部分図式への余錐の制限を正規化し、頂点に沿う輸送後の制限の Hom を計算する。
方針：図式の等式による移送を含む底上の制限へ、left fibration の transport の自然性を適用する。
規約：余極限性は共通部分の図式にだけ要求し、元の部分余錐の輸送を保つ。
使われ方：span の余錐の二枝から、共通部分の境界の連結成分の一致を導く。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {A C X : SSet.{u}} {p : A ⟶ X} (F : C ⟶ X) (i : A ⟶ C) (hi : i ≫ F = p)

/-- 部分図式の表示を正規化した、元の余錐から共通部分の余錐への制限。 -/
def normalizedCoconeRestriction : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict F i ≫ eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder hi)

/-- 正規化した制限は余錐の頂点への射影を厳密に保つ。 -/
lemma normalizedCoconeRestriction_projection :
    normalizedCoconeRestriction F i hi ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F := by
  have ht {a b : A ⟶ X} (h : a = b) :
      eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder h) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection b = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a := by
    cases h
    exact Category.id_comp _
  rw [normalizedCoconeRestriction, Category.assoc, ht hi, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection]

/-- 指定した頂点上の余錐空間への、正規化した制限。 -/
def normalizedCoconeRestrictionFiber (y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)
    (normalizedCoconeRestriction F i hi) (normalizedCoconeRestriction_projection F i hi) y

/-- 固定頂点の正規化した制限は、通常の fiber の制限と図式の等式による移送の合成。 -/
lemma normalizedCoconeRestrictionFiber_eq (y : X _⦋0⦌) :
    normalizedCoconeRestrictionFiber F i hi y = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap F i y ≫
      eqToHom (congrArg (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace a y) hi) := by
  cases hi
  simp only [normalizedCoconeRestrictionFiber, normalizedCoconeRestriction,
    eqToHom_refl, Category.comp_id]
  rfl

/-- 部分余錐を輸送してから共通部分で Hom を読むと、元の制限の Hom と底の辺の合成になる。 -/
lemma coconeMappingSpacePiZeroEquiv_restrict_transport [Quasicategory X]
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) {a b : X _⦋0⦌} (e : X.Edge a b)
    (v : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F a)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv c hc b
        (SSet.mapπ₀ (normalizedCoconeRestrictionFiber F i hi b)
          (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F) e) v)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv c hc a
          (SSet.mapπ₀ (normalizedCoconeRestrictionFiber F i hi a) v) ≫
        SSet.Truncated.HomotopyCategory.homMk e.toTruncated :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.leftFibrationInitialFiberPiZeroEquiv_map_transport (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) (normalizedCoconeRestriction F i hi)
      (normalizedCoconeRestriction_projection F i hi) c hc e v

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
