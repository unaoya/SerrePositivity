module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberwiseMappingSpaceComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Edges

/-!
概要：区間上の充満忠実性の判定を両端と前向きの写像空間へ分ける。
方針：同じ端点では fiber の比較を使い、逆向きの写像空間は空であることを使う。
規約：前向きの写像空間の同値性は入力として明示する。
使われ方：Kerodon Proposition 5.1.6.7（Tag 01VB）、cocartesian 辺による全空間比較への還元。

対応節は Kerodon 4.8（Tag 0578）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiber_quasicategory_of_innerFibration

/-- 概要：標準単体で像の順序が逆転する二頂点の写像空間は空。
方針：任意の単体を零単体へ制限し、その像の辺の単調性に矛盾させる。
規約：元の単体集合の quasicategory 性は不要。
使われ方：Kerodon Proposition 5.1.6.7（Tag 01VB）、区間の一端から零端への比較。 -/
lemma pinchedHom_isEmpty_of_stdSimplex_reverse {E : SSet.{u}} {n : ℕ}
    (p : E ⟶ (Δ[n] : SSet.{u})) (x y : E _⦋0⦌)
    (h : (p.app (Opposite.op ⦋0⦌) y) 0 < (p.app (Opposite.op ⦋0⦌) x) 0) (m : ℕ) :
    IsEmpty ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) _⦋m⦌) where
  false s := by
    let a := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y).map (SimplexCategory.const ⦋0⦌ ⦋m⦌ 0).op s
    let t := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p x y).app (Opposite.op ⦋0⦌) a
    have hm : t.val 0 ≤ t.val 1 := (stdSimplex.objEquiv t.val).toOrderHom.monotone (by decide)
    have h0 : t.val 0 = (p.app (Opposite.op ⦋0⦌) x) 0 :=
      congrArg (fun z : (Δ[n] : SSet.{u}) _⦋0⦌ ↦ z 0) t.source
    have h1 : t.val 1 = (p.app (Opposite.op ⦋0⦌) y) 0 :=
      congrArg (fun z : (Δ[n] : SSet.{u}) _⦋0⦌ ↦ z 0) t.target
    rw [h0, h1] at hm
    exact (not_le_of_gt h) hm

/-- 概要：像の順序が逆転する二頂点間では基底上の射の写像空間比較は同値。
方針：両側の写像空間が空なので、誘導射が各次数で全単射であることを使う。
規約：全空間は quasicategory、共通の基底は標準単体。
使われ方：Kerodon Proposition 5.1.6.7（Tag 01VB）、区間の逆向きの比較の除去。 -/
lemma pinchedHomMap_equivalence_of_stdSimplex_reverse
    {E F : SSet.{u}} [Quasicategory E] [Quasicategory F] {n : ℕ}
    (p : E ⟶ (Δ[n] : SSet.{u})) (q : F ⟶ Δ[n]) (f : E ⟶ F) (hf : f ≫ q = p)
    (x y : E _⦋0⦌)
    (h : (p.app (Opposite.op ⦋0⦌) y) 0 < (p.app (Opposite.op ⦋0⦌) x) 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap f x y) := by
  have he (z : E _⦋0⦌) : q.app (Opposite.op ⦋0⦌) (f.app (Opposite.op ⦋0⦌) z) =
      p.app (Opposite.op ⦋0⦌) z :=
    congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌) z) hf
  have h' : (q.app (Opposite.op ⦋0⦌) (f.app (Opposite.op ⦋0⦌) y)) 0 <
      (q.app (Opposite.op ⦋0⦌) (f.app (Opposite.op ⦋0⦌) x)) 0 := by rw [he, he]; exact h
  have happ : ∀ d, IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap f x y).app d) := by
    rintro ⟨⟨m⟩⟩
    have := pinchedHom_isEmpty_of_stdSimplex_reverse p x y h m
    have := pinchedHom_isEmpty_of_stdSimplex_reverse q _ _ h' m
    apply (isIso_iff_bijective _).mpr
    exact ⟨fun s ↦ isEmptyElim s, fun t ↦ isEmptyElim t⟩
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap f x y) := NatIso.isIso_of_isIso_app _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence.isSimplicialHomotopyEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap f x y))).isQCatEquivalence

/-- 概要：区間上の射は両端で充満忠実かつ前向きの写像空間で同値なら充満忠実。
方針：二頂点の時刻の四通りを、fiber の比較、前向きの条件、逆向きの空性で処理する。
規約：前向きの比較には零端の始点と一端の終点を指定する。
使われ方：Kerodon Proposition 5.1.6.7（Tag 01VB）、cocartesian transport による残りの比較。 -/
lemma isFullyFaithful_over_interval_of_endpoint_fibers_of_crossing
    {E F : SSet.{u}} [Quasicategory E] [Quasicategory F]
    (p : E ⟶ (Δ[1] : SSet.{u})) (q : F ⟶ Δ[1]) (f : E ⟶ F) (hf : f ≫ q = p)
    (h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
    (h1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
    (hc : ∀ x y : E _⦋0⦌,
      p.app (Opposite.op ⦋0⦌) x = stdSimplex.obj₀Equiv.symm (0 : Fin 2) →
      p.app (Opposite.op ⦋0⦌) y = stdSimplex.obj₀Equiv.symm (1 : Fin 2) →
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap f x y)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f := by
  intro x y
  obtain ⟨i, hi⟩ := stdSimplex.obj₀Equiv.symm.surjective (p.app (Opposite.op ⦋0⦌) x)
  obtain ⟨j, hj⟩ := stdSimplex.obj₀Equiv.symm.surjective (p.app (Opposite.op ⦋0⦌) y)
  fin_cases i <;> fin_cases j
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pinchedHomMap_equivalence_of_vertexFiberMap_fullyFaithful p q f hf _ h0
      ⟨x, by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_zero]; exact hi.symm⟩
      ⟨y, by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_zero]; exact hj.symm⟩
  · exact hc x y hi.symm hj.symm
  · apply pinchedHomMap_equivalence_of_stdSimplex_reverse p q f hf x y
    rw [← hi, ← hj]
    decide
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pinchedHomMap_equivalence_of_vertexFiberMap_fullyFaithful p q f hf _ h1
      ⟨x, by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_zero]; exact hi.symm⟩
      ⟨y, by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_zero]; exact hj.symm⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
