module
public import SerrePositivity.KST.SConstruction.EnrichedCompositionReplacement
public import SerrePositivity.KST.SConstruction.CoherentSimplexCompositionEdge
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MaximumFlag

/-! # 元の pinched 比較面の合成比較座標
概要：長辺から二辺の合成への Path 包含を、元の比較区間の恒等座標として読む。
方針：二つの端点 Path の最後の前頂点をそれぞれ零・一と計算する。
規約：元の区間を選び直さず、全一単体の座標射を厳密に回収する。
使われ方：保存した比較面を復号して元の BF 比較辺全体を回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 二端点だけの Path の最後の前頂点は零。 -/
lemma pinchedComparisonEndpoint_maximum :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum.{u} (n := 1) (i := (0 : Fin 2)) (coherentEndpointPath (J := ULift.{u} (Fin 3))
      (show (ULift.up (0 : Fin 3) : ULift.{u} _) ≤ ULift.up 2 from by decide)) = 0 := by
  have hp : coherentEndpointPath (J := ULift.{u} (Fin 3))
      (show (ULift.up (0 : Fin 3) : ULift.{u} _) ≤ ULift.up 2 from by decide) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.maximumFlagPath.{u} (0 : Fin 2) := by
    apply SimplicialThickening.Path.ext
    ext x
    obtain ⟨x⟩ := x
    fin_cases x <;> simp [coherentEndpointPath, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.maximumFlagPath]
  rw [hp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum_maximumFlagPath]

/-- 三頂点の合成 Path の最後の前頂点は一。 -/
lemma pinchedComparisonComposite_maximum :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum.{u} (n := 1) (i := (0 : Fin 2))
      (coherentEndpointPathComposite (J := ULift.{u} (Fin 3))
      (show (ULift.up (0 : Fin 3) : ULift.{u} _) ≤ ULift.up 1 from by decide)
      (show (ULift.up (1 : Fin 3) : ULift.{u} _) ≤ ULift.up 2 from by decide)) = 1 := by
  have hp : coherentEndpointPathComposite (J := ULift.{u} (Fin 3))
      (show (ULift.up (0 : Fin 3) : ULift.{u} _) ≤ ULift.up 1 from by decide)
      (show (ULift.up (1 : Fin 3) : ULift.{u} _) ≤ ULift.up 2 from by decide) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.maximumFlagPath.{u} (1 : Fin 2) := by
    apply SimplicialThickening.Path.ext
    ext x
    obtain ⟨x⟩ := x
    fin_cases x <;> simp [coherentEndpointPathComposite, coherentEndpointPath, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.maximumFlagPath]
  rw [hp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum_maximumFlagPath]

/-- 元の合成比較 Path の全一単体は、pinched 比較の元の恒等区間に写る。 -/
lemma pinchedComparisonCoordinate_edge :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap.{u} (0 : Fin 2)).app (Opposite.op ⦋1⦌)
      (nerve.edgeMk (coherentEndpointPathToComposite (J := ULift.{u} (Fin 3))
        (show (ULift.up (0 : Fin 3) : ULift.{u} _) ≤ ULift.up 1 from by decide)
        (show (ULift.up (1 : Fin 3) : ULift.{u} _) ≤ ULift.up 2 from by decide))).edge =
      SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by
  apply stdSimplex.ext
  intro i
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap.{u} (0 : Fin 2)).app (Opposite.op ⦋1⦌) _).down.toOrderHom i = i
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap_apply]
  fin_cases i
  · exact pinchedComparisonEndpoint_maximum
  · exact pinchedComparisonComposite_maximum

end SerrePositivity.KST.SConstruction
