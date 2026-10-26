module

public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleSeparatedSimplexDiagonal

/-!
概要：再構成した全二胞体族の長辺は、元の長 Hom の直接評価の標準 coherent 区間族。
方針：全次数の豊穣関手の照合を、同じ K・L の全族の射の等号へ束ねる。
規約：K の頂点だけでなく全単体に対する厳密等号。
使われ方：採用済みの正規化後の全対角条項。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma triangleSeparatedFamily_diagonal
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C}
    {K L : SSet.{max u v}}
    (f : K ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y))
    (g : K ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z))
    (M : (Δ[1] : SSet.{max u v}) ⊗ ((K ⊗ K) ⊗ L) ⟶
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Z))
    (hM : prismEndpoint 1 ((K ⊗ K) ⊗ L) ≫ M =
      lift (fst (K ⊗ K) L ≫ fst K K ≫ f) (fst (K ⊗ K) L ≫ snd K K ≫ g) ≫
      (HomotopyLimits.uliftTensorIso.{u, v}
        (SimplicialCategory.sHom X Y) (SimplicialCategory.sHom Y Z)).inv ≫
        (SSet.uliftFunctor.{v, u}).map (eComp SSet X Y Z))
    (q : (Δ[1] : SSet.{max u v}) ⊗ (K ⊗ L) ⟶
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Z))
    (hdiag : (Δ[1] ◁ triangleParameterDiagonal K L) ≫ M = q) :
    (stdSimplex.δ (1 : Fin 3) ▷ (K ⊗ L)) ≫ triangleSeparatedFamily f g M hM =
      (Δ[1] ◁ (prismEndpoint 0 (K ⊗ L) ≫ q)) ≫
        intervalMappingUncurry (coherentHomIntervalComparison X Z) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, s, r⟩
  change triangleSeparatedSimplex f g M hM s r
      (triangleDiagonalLabel (stdSimplex.objEquiv t).toOrderHom) =
    (intervalMappingUncurry (coherentHomIntervalComparison X Z)).app (Opposite.op ⦋n⦌)
      (t, ULift.up (((prismEndpoint 0 (K ⊗ L) ≫ q).app (Opposite.op ⦋n⦌) (s, r)).down))
  rw [triangleSeparatedSimplex_diagonal f g M hM q hdiag s r,
    coherentHomIntervalComparison_evaluate_cut]

end SerrePositivity.InfinityCategories
