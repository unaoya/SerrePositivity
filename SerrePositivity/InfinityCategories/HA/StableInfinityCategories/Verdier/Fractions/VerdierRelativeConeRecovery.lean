module


public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyNatTrans
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.HomotopyPrecompVertex

/-!
概要：有限図式上の商錐を、パラメータ全体と元の境界を保持して回収する条件を表す。
方針：積上の実図式と境界固定の可逆比較円柱を一つのデータにまとめる。
規約：任意の有限試験図式を許し、対象の持ち上げだけでは代用しない。
使われ方：c5 の標準単体の次元帰納と元の core 逆像射影の slice の有限錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants

structure VerdierRelativeConeRecovery {X Y : SSet.{u}} (q : X ⟶ Y)
    (K S : SSet.{u}) (p : K ⊗ S ⟶ X)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ⊗ S ⟶ Y) where
  diagram : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ⊗ S ⟶ X
  boundary : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K ▷ S) ≫ diagram = p
  comparison : SSet.Homotopy (diagram ≫ q) H
  fixed : ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K ▷ S) ▷ (Δ[1] : SSet.{u})) ≫ comparison.h =
    fst (K ⊗ S) Δ[1] ≫ (p ≫ q)
  invertible : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge comparison x).toTruncated

def HasVerdierRelativeConeRecovery {X Y : SSet.{u}} (q : X ⟶ Y) (S : SSet.{u}) : Prop :=
  ∀ (K : SSet.{u}) [K.Finite] (p : K ⊗ S ⟶ X)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ⊗ S ⟶ Y),
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K ▷ S) ≫ H = p ≫ q →
      Nonempty (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.VerdierRelativeConeRecovery q K S p H)

/-- 時間に定値な実比較は、各頂点で可逆である。 -/
lemma relativeConeComparison_invertible_of_constant {T Y : SSet.{u}}
    {f g : T ⟶ Y} (H : SSet.Homotopy f g)
    (hh : H.h = fst T (Δ[1] : SSet.{u}) ≫ g) :
    ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated := by
  intro x
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).edge =
      (Truncated.Edge.id (X := (truncation 2).obj Y) (g.app (Opposite.op ⦋0⦌) x)).edge := by
    change H.h.app (Opposite.op ⦋1⦌)
      ((Truncated.Edge.id (X := (truncation 2).obj T) x).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
    rw [hh]
    change g.app (Opposite.op ⦋1⦌) (T.σ 0 x) = Y.σ 0 (g.app (Opposite.op ⦋0⦌) x)
    exact g.naturality_apply (SimplexCategory.σ (0 : Fin 1)).op x
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr
  change IsIso (Truncated.HomotopyCategory.homMk (Truncated.Edge.id _))
  rw [Truncated.HomotopyCategory.homMk_id]
  infer_instance

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
