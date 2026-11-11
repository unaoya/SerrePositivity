module
public import SerrePositivity.KST.Fibration.VerdierMovingUpperVertexColumns

/-!
概要：動く実上側族の三頂点の縦辺が恒等辺であることを回収する。
方針：同じ全区間列の定値性を全一単体で評価する。
規約：第二短辺の動く全比較を保持し、新しい可逆性仮定を加えない。
使われ方：K-6 c4 の正規化全四角柱の可逆性への上側入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (ℓ : (verdierMovingUpperLongSpace d) _⦋0⦌)

/-- 概要：同じ動く実上側族を両端間の実ホモトピーとして読む。
方針：元の全族の二端点制限を使う。
規約：同じ三角柱を保持。使われ方：全三頂点の縦辺可逆性判定。 -/
def verdierMovingUpperHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) where
  h := verdierMovingUpperFamily d ℓ
  h₀ := rfl
  h₁ := rfl
  rel := by ext n t; exact False.elim t.1.2

/-- 概要：上側全族の各頂点の縦辺は元の同じ対象の恒等一単体。
方針：三つの全区間列の定値回収を同じ一単体へ適用する。
規約：三角形全体の定値性は要求しない。
使われ方：全上側縦辺の無条件の可逆性。 -/
theorem verdierMovingUpperHomotopy_vertex_constant (x : (Δ[2] : SSet.{u + 1}) _⦋0⦌) :
    ∃ v : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierMovingUpperHomotopy d ℓ) x).edge =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1 := by
  have he (j : Fin 3) (i : Fin 2) (v : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
      (h : ((stdSimplex.δ i ≫ stdSimplex.δ j) ▷ (Δ[1] : SSet.{u + 1})) ≫
        verdierMovingUpperFamily d ℓ =
        fst (Δ[0] : SSet.{u + 1}) Δ[1] ≫ SSet.yonedaEquiv.symm v) :
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierMovingUpperHomotopy d ℓ)
        ((stdSimplex.δ i ≫ stdSimplex.δ j).app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))).edge = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1 := by
    have hh := congrArg (fun f : (Δ[0] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} =>
      f.app (Opposite.op ⦋1⦌)
        (((Δ[0] : SSet.{u + 1}).σ 0 (stdSimplex.obj₀Equiv.symm (0 : Fin 1))),
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) h
    change (verdierMovingUpperFamily d ℓ).app (Opposite.op ⦋1⦌)
      ((stdSimplex.δ i ≫ stdSimplex.δ j).app (Opposite.op ⦋1⦌)
        ((Δ[0] : SSet.{u + 1}).σ 0 (stdSimplex.obj₀Equiv.symm (0 : Fin 1))),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _ at hh
    rw [σ_naturality_apply] at hh
    exact hh
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  fin_cases i
  · exact ⟨_, he 2 1 _ (verdierMovingUpperFamily_source_column d ℓ)⟩
  · exact ⟨_, he 2 0 _ (verdierMovingUpperFamily_middle_column d ℓ)⟩
  · exact ⟨_, he 0 0 _ (verdierMovingUpperFamily_target_column d ℓ)⟩

/-- 概要：動く実上側族は全三頂点で可逆な縦辺を持つ。
方針：各縦辺の元の恒等一単体への厳密回収を使う。
規約：可逆性入力なし。使われ方：同じ実四角柱の全関手比較。 -/
theorem verdierMovingUpperHomotopy_pointwise :
    ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
      (verdierMovingUpperHomotopy d ℓ) x).toTruncated := by
  intro x
  obtain ⟨v, hv⟩ := verdierMovingUpperHomotopy_vertex_constant d ℓ x
  have h : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierMovingUpperHomotopy d ℓ) x).toTruncated.edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) v).edge :=
    hv.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr h).mpr
  change IsIso (SSet.Truncated.HomotopyCategory.homMk
    (SSet.Truncated.Edge.id (X := (truncation 2).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) v))
  rw [SSet.Truncated.HomotopyCategory.homMk_id]
  infer_instance

end SerrePositivity.KST.Fibration
