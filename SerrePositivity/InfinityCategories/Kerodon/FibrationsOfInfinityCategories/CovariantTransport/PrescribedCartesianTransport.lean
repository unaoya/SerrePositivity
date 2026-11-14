module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.CartesianHomotopyExtension
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.VertexDiscrete

/-!
概要：元の指定辺を全頂点で固定する Cartesian な輸送 prism を構成する。
方針：全頂点で固定した相対延長と Cartesian 辺の消去則を使用する。
規約：指定した元の置換の比較射を変更しない。使われ方：HTT 5.2.4.6 の cf 比較。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
noncomputable section

/-- 全頂点の区間の辺を、離散的な頂点パラメータの区間族へ束ねる。 -/
def vertexEdgeFamily {A E : SSet.{u}} (e : A _⦋0⦌ → ((Δ[1] : SSet.{u}) ⟶ E)) :
    (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete A ⟶ E where
  app n := ↾fun z ↦ (e z.2).app n z.1
  naturality {i j} f := by
    apply ConcreteCategory.hom_ext
    intro z
    exact (e z.2).naturality_apply f z.1

/-- 元の全頂点の辺を変更せず、同じ終点・底を持つ Cartesian prism へ延長する。 -/
lemma exists_cartesianPrism_prescribed_vertices {A E : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration p] (f : A ⟶ E)
    (hf : f ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (x : A _⦋0⦌ → E _⦋0⦌)
    (e : ∀ v, E.Edge (x v) (f.app (Opposite.op ⦋0⦌) v))
    (he : ∀ v, p.app (Opposite.op ⦋1⦌) (e v).edge = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)
    (hc : ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (e v).edge) :
    ∃ H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H = f ∧ H ≫ p = fst (Δ[1] : SSet.{u}) A ∧
      (∀ v : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1))) ∧
      (∀ v : A _⦋0⦌, H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1) = (e v).edge) := by
  let g := vertexEdgeFamily (fun v ↦ SSet.yonedaEquiv.symm (e v).edge)
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete A) ≫ g = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι A ≫ f := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro v
    change (SSet.yonedaEquiv.symm (e v).edge).app (Opposite.op ⦋n⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) n) =
      f.app (Opposite.op ⦋n⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v n)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map]
    congr 1
    have htgt := stdSimplex.yonedaEquiv_δ_comp (SSet.yonedaEquiv.symm (e v).edge) 0
    simp only [stdSimplex.δ_zero_eq_const, SSet.const_comp, SSet.yonedaEquiv_const,
      Equiv.apply_symm_apply] at htgt
    exact htgt.trans (e v).tgt_eq
  have hb : g ≫ p = (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι A) ≫ fst (Δ[1] : SSet.{u}) A := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨t, v⟩
    change ((SSet.yonedaEquiv.symm (e v).edge) ≫ p).app n t = t
    have h := congrArg SSet.yonedaEquiv.symm (he v)
    rw [← SSet.yonedaEquiv_symm_comp] at h
    rw [h]
    have hi : SSet.yonedaEquiv.symm _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge =
        (𝟙 (Δ[1] : SSet.{u})) := by
      apply SSet.yonedaEquiv.injective
      rw [Equiv.apply_symm_apply]
      apply SSet.stdSimplex.ext
      intro i
      fin_cases i <;> rfl
    rw [hi]
    rfl
  have hg : ∀ v : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete A) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p
      (g.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1)) := by
    intro v
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p ((SSet.yonedaEquiv.symm (e v).edge).app _
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))))
    rw [SSet.yonedaEquiv_symm_app_id]
    exact hc v
  obtain ⟨H, hH, h1, hp, hcart⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cartesianHomotopy_extend p (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι A) g f
    (fst (Δ[1] : SSet.{u}) A) ht (by simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, lift_fst] using hf) hb hg
  refine ⟨H, h1, hp, hcart, ?_⟩
  intro v
  have h := congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌)
    (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), v)) hH
  change H.app (Opposite.op ⦋1⦌)
    (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1) =
      (SSet.yonedaEquiv.symm (e v).edge).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) at h
  rwa [SSet.yonedaEquiv_symm_app_id] at h

end
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
