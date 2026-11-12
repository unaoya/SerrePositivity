module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.F1CocartesianTrianglePrism

/-!
概要：底の三角形に沿う covariant transport 関手の合成。
方針：二つの証人の prism を貼り、三角形の prism の長辺を証人に取る。
規約：transport は指定した端点の fiber 間の単体集合の射。
使われ方：Kerodon Proposition 5.2.5.1（Tag 01VU）、Construction 5.2.5.2（Tag 019U） の合成則。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：三角形の二辺に沿う transport の関手の合成は長辺に沿う transport。
方針：後半の証人を最初の関手で前合成し、二辺の prism を三角形に延長する。
規約：cocartesian fibration の全ての持ち上げの存在は不要、inner fibration で十分。
使われ方：Kerodon Proposition 5.2.5.1（Tag 01VU）、選択した transport の合成の比較。 -/
lemma IsEdgeTransport.comp {X B : SSet.{u}} [Quasicategory B] (p : X ⟶ B)
    [InnerFibration p] {a b c : B _⦋0⦌}
    {e : SSet.Edge (X := B) a b} {f : SSet.Edge (X := B) b c}
    {g : SSet.Edge (X := B) a c} (σ : SSet.Edge.CompStruct e f g)
    {F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b} {G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c}
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsEdgeTransport p e F) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsEdgeTransport p f G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsEdgeTransport p g (F ≫ G) := by
  obtain ⟨H₀₁, hF₀, hF₁, hFp, hFc⟩ := hF
  obtain ⟨H₁₂, hG₀, hG₁, hGp, hGc⟩ := hG
  let A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a
  let H' := (Δ[1] ◁ F) ≫ H₁₂
  let b' := fst (Δ[2] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm σ.simplex
  have hw : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H₀₁ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H' := by
    dsimp only [H']
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hG₀, hF₁]
  have hp₀₁ : H₀₁ ≫ p = (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ b' := by
    rw [hFp]
    change fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge =
      (fst (Δ[1] : SSet.{u}) A ≫ stdSimplex.δ (2 : Fin 3)) ≫
        SSet.yonedaEquiv.symm σ.simplex
    rw [Category.assoc, σ.δ_two_yonedaEquiv_symm]
  have hp₁₂ : H' ≫ p = (stdSimplex.δ (0 : Fin 3) ▷ A) ≫ b' := by
    dsimp only [H']
    rw [Category.assoc, hGp]
    change fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm f.edge =
      (fst (Δ[1] : SSet.{u}) A ≫ stdSimplex.δ (0 : Fin 3)) ≫
        SSet.yonedaEquiv.symm σ.simplex
    rw [Category.assoc, σ.δ_zero_yonedaEquiv_symm]
  obtain ⟨T, hT₀₁, hT₁₂, hTp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.innerFibration_fillTrianglePrism p H₀₁ H' b' hw hp₀₁ hp₁₂
  let H := (stdSimplex.δ (1 : Fin 3) ▷ A) ≫ T
  have hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ (stdSimplex.δ (2 : Fin 3) ▷ A) := by rfl
  have ho : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ (stdSimplex.δ (0 : Fin 3) ▷ A) := by rfl
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · dsimp only [H]
    rw [← Category.assoc, hz, Category.assoc, hT₀₁]
    exact hF₀
  · dsimp only [H]
    rw [← Category.assoc, ho, Category.assoc, hT₁₂]
    dsimp only [H']
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hG₁,
      Category.assoc]
  · dsimp only [H]
    rw [Category.assoc, hTp]
    change (fst (Δ[1] : SSet.{u}) A ≫ stdSimplex.δ (1 : Fin 3)) ≫
      SSet.yonedaEquiv.symm σ.simplex = _
    rw [Category.assoc, σ.δ_one_yonedaEquiv_symm]
    rfl
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianTrianglePrism_longEdge p T
    · intro v
      rw [hT₀₁]
      exact hFc v
    · intro v
      rw [hT₁₂]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (H₁₂.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})),
          F.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1)))
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map]
      exact hGc (F.app (Opposite.op ⦋0⦌) v)

/-- 概要：選択した長辺の transport は二辺の transport の合成と同型。
方針：合成が transport であることを証人の一意性と組み合わせる。
規約：同型は終点 fiber の関手単体集合のホモトピー圏で取る。
使われ方：Kerodon Proposition 5.2.5.1（Tag 01VU）、Construction 5.2.5.2（Tag 019U） の合成の整合性。 -/
lemma edgeTransport_composition_iso {X B : SSet.{u}} [Quasicategory B] (p : X ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] {a b c : B _⦋0⦌}
    {e : SSet.Edge (X := B) a b} {f : SSet.Edge (X := B) b c}
    {g : SSet.Edge (X := B) a c} (σ : SSet.Edge.CompStruct e f g) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p f)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsEdgeTransport.functorIso p g (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_isTransport p g)
    (IsEdgeTransport.comp p σ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_isTransport p e) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_isTransport p f))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
