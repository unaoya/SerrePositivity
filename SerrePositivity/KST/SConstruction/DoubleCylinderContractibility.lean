module
public import SerrePositivity.KST.SConstruction.PointedContractibility
public import SerrePositivity.KST.Comparison.DoubleMappingCylinderEquivalence
public import SerrePositivity.KST.Comparison.DoubleMappingCylinderCollapse
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction

/-! # 可縮な三成分の二重円筒の弱可縮性
概要：左右の脚の単射性なしに、三成分が可縮な二重円筒を一点と比較する。
方針：一点の span への比較と二重円筒の局所化不変性を使う。
規約：円筒の Kan 性は主張せず、Kan 置換後に全境界の充填を得る。
使われ方：構造射の自然性の可縮なパラメーター空間。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open Comparison Spectra
open scoped Simplicial

/-- 可縮 Kan 複体の一点への射は anodyne 局所化で同型。 -/
lemma contractibleKan_toUnit_localized_isIso {K : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan K) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toUnit K)) := by
  have ht := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_iff_trivialKanFibration K).mp hK
  have : IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from K)) :=
    MonoRightLiftingContraction.localized_isIso _ ht.mem
  let e : terminal SSet.{u} ≅ 𝟙_ SSet.{u} :=
    terminalIsTerminal.uniqueUpToIso isTerminalTensorUnit
  have h : toUnit K = terminal.from K ≫ e.hom := isTerminalTensorUnit.hom_ext _ _
  rw [h, Functor.map_comp]
  infer_instance

/-- 一点の span の二重円筒は局所化で一点と同型。 -/
lemma pointDoubleCylinder_toUnit_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (toUnit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder (𝟙 (𝟙_ SSet.{u})) (𝟙 (𝟙_ SSet.{u}))))) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  let f := 𝟙 (𝟙_ SSet.{u})
  let P := pushout f f
  have : IsIso (Q.map (pushout.inr f f)) := by infer_instance
  have hP : IsIso (Q.map (toUnit P)) := by
    have h : pushout.inr f f ≫ toUnit P = 𝟙 (𝟙_ SSet.{u}) := isTerminalTensorUnit.hom_ext _ _
    have hc : IsIso (Q.map (pushout.inr f f) ≫ Q.map (toUnit P)) := by
      rw [← Functor.map_comp, h]
      infer_instance
    exact (isIso_comp_left_iff _ _).mp hc
  have : IsIso (Q.map (doubleMappingCylinderCollapse f f)) :=
    doubleMappingCylinderCollapse_localized_isIso f f
  have h : toUnit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder f f) = doubleMappingCylinderCollapse f f ≫ toUnit P :=
    isTerminalTensorUnit.hom_ext _ _
  change IsIso (Q.map (toUnit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder f f)))
  rw [h, Functor.map_comp]
  infer_instance

/-- 三成分が可縮 Kan な任意の span の二重円筒は局所化で一点と同型。 -/
lemma doubleCylinder_toUnit_localized_isIso {C A B : SSet.{u}} (f : C ⟶ A) (g : C ⟶ B)
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan C) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan A) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan B) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder f g))) := by
  let q := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap f g (𝟙 (𝟙_ SSet.{u})) (𝟙 (𝟙_ SSet.{u}))
    (toUnit C) (toUnit A) (toUnit B)
    (isTerminalTensorUnit.hom_ext _ _) (isTerminalTensorUnit.hom_ext _ _)
  have : IsIso (AnodyneHomotopy.anodyneQ.map q) :=
    doubleMappingCylinderMap_localized_isIso _ _ _ _ _ _ _ _ _
      (contractibleKan_toUnit_localized_isIso hC)
      (contractibleKan_toUnit_localized_isIso hA) (contractibleKan_toUnit_localized_isIso hB)
  have := pointDoubleCylinder_toUnit_localized_isIso.{u}
  have h : toUnit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder f g) = q ≫ toUnit _ := isTerminalTensorUnit.hom_ext _ _
  rw [h, Functor.map_comp]
  infer_instance

/-- 一点と局所化同値な非空単体集合の Kan 置換は全境界を充填する。 -/
lemma kanReplacement_contractible_of_localized_toUnit {D : SSet.{u}} (d : D _⦋0⦌)
    (hD : IsIso (AnodyneHomotopy.anodyneQ.map (toUnit D))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (AnodyneKanReplacement.functor.obj D) := by
  let P : PointedSimplicialSet.{u} := Under.mk (SSet.const d)
  let Z := PointedKanReplacement.obj P
  have hi : IsIso (AnodyneHomotopy.anodyneQ.map (AnodyneKanReplacement.unit.app D)) :=
    (Localization.inverts AnodyneHomotopy.anodyneQ anodyneExtensions) _
      (AnodyneKanReplacement.unit_anodyne D)
  have h : AnodyneKanReplacement.unit.app D ≫ toUnit Z.right = toUnit D :=
    isTerminalTensorUnit.hom_ext _ _
  have hc : IsIso (AnodyneHomotopy.anodyneQ.map (AnodyneKanReplacement.unit.app D) ≫
      AnodyneHomotopy.anodyneQ.map (toUnit Z.right)) := by
    rw [← Functor.map_comp, h]
    exact hD
  exact pointedIsContractibleKan_of_localized_toPoint Z ((isIso_comp_left_iff _ _).mp hc)

end SerrePositivity.KST.SConstruction
