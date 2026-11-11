module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CosliceFiberDiagramChange
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IntervalFullyFaithfulCriterion
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberwiseEssentialSurjectivity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful

/-!
概要：選択した cocartesian lift により区間上の fiber ごとの同値を全空間へ移す。
方針：三角形の両射影で前向きの写像空間を比較し、両端の比較と組み合わせる。
規約：全ての cocartesian 辺を保つ条件の代わりに、零端の各頂点で保たれる lift を明示する。
使われ方：Kerodon Proposition 5.1.6.7（Tag 01VB）、Theorem 5.1.6.1（Tag 023M）、Theorem 5.2.4.1（Tag 024N） の区間上の判定。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiber_quasicategory_of_innerFibration

/-- 概要：保存される cocartesian 辺はその終点側の写像空間の同値を始点側へ移す。
方針：点の coslice の同値条件を右 pinched 写像空間へ移して三角形の比較定理を使う。
規約：辺は共通の標準区間の恒等辺を被覆し、終点 y は時刻一。
使われ方：Kerodon Proposition 5.1.6.7（Tag 01VB）、前向きの写像空間の充満忠実性。 -/
lemma cocartesian_crossing_mapping_equivalence_of_target
    {E F : SSet.{u}} [Quasicategory E] [Quasicategory F]
    (p : E ⟶ (Δ[1] : SSet.{u})) (q : F ⟶ Δ[1]) (f : E ⟶ F) (hf : f ≫ q = p)
    (e : (Δ[1] : SSet.{u}) ⟶ E) (hp : e ≫ p = 𝟙 Δ[1])
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (SSet.yonedaEquiv e))
    (hef : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (SSet.yonedaEquiv (e ≫ f)))
    (y : E _⦋0⦌) (hy : p.app (Opposite.op ⦋0⦌) y = stdSimplex.obj₀Equiv.symm (1 : Fin 2))
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap f (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ e)) y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap f (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ e)) y) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.coslicePostcompFiberMap_equivalence_iff_pinchedHomMap (stdSimplex.δ 1 ≫ e) f y).mp
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.coslicePostcompFiberMap_source_equivalence_of_target p q f hf e hp he hef y hy
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.coslicePostcompFiberMap_equivalence_iff_pinchedHomMap (stdSimplex.δ 0 ≫ e) f y).mpr ht

/-- 概要：両端で充満忠実かつ各零頂点で保存される cocartesian lift がある区間上の射は充満忠実。
方針：前向きの二頂点間の比較を選択 lift の終点側へ移し、一端の fiber の比較で判定する。
規約：lift の始点と区間への像は厳密な射の等式で指定する。
使われ方：Kerodon Proposition 5.1.6.7（Tag 01VB）、写像円柱比較の前向きの写像空間の判定。 -/
lemma isFullyFaithful_over_interval_of_endpoint_fibers_of_cocartesian_lifts
    {E F : SSet.{u}} [Quasicategory E] [Quasicategory F]
    (p : E ⟶ (Δ[1] : SSet.{u})) (q : F ⟶ Δ[1]) (f : E ⟶ F) (hf : f ≫ q = p)
    (h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
    (h1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
    (hl : ∀ x : E _⦋0⦌,
      p.app (Opposite.op ⦋0⦌) x = stdSimplex.obj₀Equiv.symm (0 : Fin 2) →
      ∃ e : (Δ[1] : SSet.{u}) ⟶ E,
        stdSimplex.δ 1 ≫ e = SSet.yonedaEquiv.symm x ∧ e ≫ p = 𝟙 Δ[1] ∧
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (SSet.yonedaEquiv e) ∧
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (SSet.yonedaEquiv (e ≫ f))) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_over_interval_of_endpoint_fibers_of_crossing p q f hf h0 h1
  intro x y hx hy
  obtain ⟨e, hs, hp, he, hef⟩ := hl x hx
  have hsx : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ e) = x := by
    rw [hs, Equiv.apply_symm_apply]
  have ht : p.app (Opposite.op ⦋0⦌)
      (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ e)) =
        stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by
    rw [← SSet.yonedaEquiv_comp, Category.assoc, hp, Category.comp_id]
    rw [stdSimplex.δ_zero_eq_const, SSet.yonedaEquiv_const]
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pinchedHomMap_equivalence_of_vertexFiberMap_fullyFaithful p q f hf _ h1
    ⟨SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ e), by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_zero]; exact ht⟩
    ⟨y, by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_zero]; exact hy⟩
  have hxy := cocartesian_crossing_mapping_equivalence_of_target p q f hf e hp he hef y hy hc
  rwa [hsx] at hxy

/-- 概要：区間上の射は両端で同値かつ保存される cocartesian lift を持てば全空間で同値。
方針：選択 lift による充満忠実性と fiber ごとの本質的全射性を組み合わせる。
規約：比較関手が保つ lift を零端の各頂点で一つ指定できればよい。
使われ方：Kerodon Theorem 5.1.6.1（Tag 023M）、Theorem 5.2.4.1（Tag 024N） の区間上の全空間判定。 -/
lemma isQCatEquivalence_over_interval_of_endpoint_fibers_of_cocartesian_lifts
    {E F : SSet.{u}} [Quasicategory E] [Quasicategory F]
    (p : E ⟶ (Δ[1] : SSet.{u})) (q : F ⟶ Δ[1]) (f : E ⟶ F) (hf : f ≫ q = p)
    (h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
    (h1 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
    (hl : ∀ x : E _⦋0⦌,
      p.app (Opposite.op ⦋0⦌) x = stdSimplex.obj₀Equiv.symm (0 : Fin 2) →
      ∃ e : (Δ[1] : SSet.{u}) ⟶ E,
        stdSimplex.δ 1 ≫ e = SSet.yonedaEquiv.symm x ∧ e ≫ p = 𝟙 Δ[1] ∧
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (SSet.yonedaEquiv e) ∧
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (SSet.yonedaEquiv (e ≫ f))) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective f
  · exact isFullyFaithful_over_interval_of_endpoint_fibers_of_cocartesian_lifts
      p q f hf h0.isFullyFaithful h1.isFullyFaithful hl
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isEssentiallySurjective_over_interval_of_endpoint_fibers p q f hf
      h0.choose.isEssentiallySurjective h1.choose.isEssentiallySurjective

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
