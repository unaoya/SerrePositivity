module

public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleSeparatedDirectHom
public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleLiftedHom

/-!
概要：中間対象を通らない長 Hom は、元の区間族の直接評価を同じ有限座標で読む。
方針：全次数の直接 Hom 回収式を、元の小さい Hom へ降ろす。
規約：単体の一頂点への制限ではない。
使われ方：再構成した全対角と標準 coherent 区間族の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma triangleSeparatedLongHom_direct_eq
    {K L : SSet.{max u v}} {H : SSet.{u}}
    (M : (Δ[1] : SSet.{max u v}) ⊗ ((K ⊗ K) ⊗ L) ⟶ (SSet.uliftFunctor.{v, u}).obj H)
    (q : (Δ[1] : SSet.{max u v}) ⊗ (K ⊗ L) ⟶ (SSet.uliftFunctor.{v, u}).obj H)
    (hM : (Δ[1] ◁ triangleParameterDiagonal K L) ≫ M = q)
    {n : ℕ} (s : K _⦋n⦌) (r : L _⦋n⦌) (t : Fin (n + 1) →o Fin 3)
    {i j : Fin (n + 1)} (hi : t i = 0)
    (hP : ∀ P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j),
      ¬ ∃ k : Fin (n + 1), ULift.up k ∈ P.I ∧ t k = 1) :
    triangleSeparatedLongHom M s r t hi j =
      triangleLiftedHom
        (pathCutLastZeroMap (triangleZeroLabel t) (triangleZeroLabel_zero t hi) j)
        (s, r) (prismEndpoint 0 (K ⊗ L) ≫ q) := by
  apply (SSet.uliftFunctor.{v, u}).map_injective
  rw [triangleSeparatedLongHom_of_no_middle M q hM s r t hi hP, triangleLiftedHom_map]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  rfl

end SerrePositivity.InfinityCategories
