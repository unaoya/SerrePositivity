module
public import SerrePositivity.KST.Fibration.VerdierLowerCanonicalShortFaces

/-!
概要：正規化下側の縦辺を元の実下側の縦辺へ厳密に回収する。
方針：同じ全二短辺が三頂点を覆うことを使い、全一単体を比較する。
規約：正規化前後の全三角柱の等号を要求しない。
使われ方：K-6 c4 の正規化四角柱の縦辺可逆性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (ℓ : (verdierLowerCanonicalLongSpace d) _⦋0⦌)

/-- 概要：正規化下側の各縦辺は元の実下側の同じ全一単体。
方針：同じ二短辺の全族等式を三頂点に評価する。
規約：元の全 native Hom と独立に、縦辺そのものを厳密回収する。
使われ方：元の恒等縦辺の可逆性を正規化側へ渡す。 -/
theorem verdierLowerCanonicalFamily_vertex_edge (x : (Δ[2] : SSet.{u + 1}) _⦋0⦌) :
    (verdierLowerCanonicalFamily d ℓ).app (Opposite.op ⦋1⦌)
      (((Δ[2] : SSet.{u + 1}).σ 0 x), _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) =
    (verdierFullSLowerDeformation d).h.app (Opposite.op ⦋1⦌)
      (((Δ[2] : SSet.{u + 1}).σ 0 x), _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) := by
  have he (j : Fin 3)
      (h : (stdSimplex.δ j ▷ (Δ[1] : SSet.{u + 1})) ≫ verdierLowerCanonicalFamily d ℓ =
        (stdSimplex.δ j ▷ (Δ[1] : SSet.{u + 1})) ≫ (verdierFullSLowerDeformation d).h)
      (a : (Δ[1] : SSet.{u + 1}) _⦋0⦌) :
      (verdierLowerCanonicalFamily d ℓ).app (Opposite.op ⦋1⦌)
        (((Δ[2] : SSet.{u + 1}).σ 0 ((stdSimplex.δ j).app (Opposite.op ⦋0⦌) a)),
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) =
      (verdierFullSLowerDeformation d).h.app (Opposite.op ⦋1⦌)
        (((Δ[2] : SSet.{u + 1}).σ 0 ((stdSimplex.δ j).app (Opposite.op ⦋0⦌) a)),
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) := by
    have hh := congrArg (fun f : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} =>
      f.app (Opposite.op ⦋1⦌)
      (((Δ[1] : SSet.{u + 1}).σ 0 a), _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) h
    change (verdierLowerCanonicalFamily d ℓ).app (Opposite.op ⦋1⦌)
      ((stdSimplex.δ j).app (Opposite.op ⦋1⦌) ((Δ[1] : SSet.{u + 1}).σ 0 a),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _ at hh
    rw [σ_naturality_apply] at hh
    exact hh
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  fin_cases i
  · exact he 2 (verdierLowerCanonicalFamily_first d ℓ) (stdSimplex.obj₀Equiv.symm 0)
  · exact he 2 (verdierLowerCanonicalFamily_first d ℓ) (stdSimplex.obj₀Equiv.symm 1)
  · exact he 0 (verdierLowerCanonicalFamily_last d ℓ) (stdSimplex.obj₀Equiv.symm 1)

/-- 概要：同じ正規化下側全族を両端間の実ホモトピーとして読む。
方針：元の全族の区間両端制限を使う。
規約：同じ三角柱そのものを保持。使われ方：縦辺の可逆性判定。 -/
def verdierLowerCanonicalHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierLowerCanonicalFamily d ℓ) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierLowerCanonicalFamily d ℓ) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) where
  h := verdierLowerCanonicalFamily d ℓ
  h₀ := rfl
  h₁ := rfl
  rel := by ext n t; exact False.elim t.1.2

/-- 概要：同じ正規化下側全族は三頂点すべてで可逆な縦辺を持つ。
方針：元の実下側の縦辺への厳密回収と元の可逆性を使う。
規約：新たな可逆性仮定なし。使われ方：貼った実四角柱の下側縦辺。 -/
theorem verdierLowerCanonicalHomotopy_pointwise :
    ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
      (verdierLowerCanonicalHomotopy d ℓ) x).toTruncated := by
  intro x
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierLowerCanonicalHomotopy d ℓ) x).toTruncated)
    (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierFullSLowerDeformation d) x).toTruncated) ?_).mpr
      (verdierFullSLowerDeformation_pointwise d x)
  exact verdierLowerCanonicalFamily_vertex_edge d ℓ x

/-- 概要：正規化下側の両端は同じ実全族から全関手同型で結ばれる。
方針：元の同じ三角柱の縦辺可逆性を適用する。
規約：元の未正規化端点との照合は別に保持する。
使われ方：正規化四角柱の全関手比較への下側入力。 -/
def verdierLowerCanonicalEndpointIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierLowerCanonicalFamily d ℓ) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierLowerCanonicalFamily d ℓ) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy _ (verdierLowerCanonicalHomotopy_pointwise d ℓ)

end SerrePositivity.KST.Fibration
