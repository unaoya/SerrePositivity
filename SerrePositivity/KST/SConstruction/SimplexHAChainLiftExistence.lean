module
public import SerrePositivity.KST.SConstruction.SimplexHAEndpointConcatDefect
public import SerrePositivity.KST.SConstruction.SimplexHAZeroEdgeCommutation

/-! # 元の native HA 単体からの全次元の実 Hom 鎖射
概要：元の任意の HA 単体と頂点列について、全次数の線形復元を回収する実鎖射を得る。
方針：最高生成元は HA 方程式、内部零・一端点は全小次元の実鎖射による強い帰納。
規約：全生成元・実微分を保持し、鎖射性を追加仮定に置かない。使われ方：逆 dg Hom 射。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 任意の元の native HA 単体から、全次元で同じ線形復元を回収する実 Hom 鎖射を得る。 -/
lemma simplexHAChainLift_exists {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) (M : ℕ) :
    SimplexHAChainLiftExists A s.toSimplexData M := by
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro v b hb
    have hd : ∀ k, simplexHADegreeDefect A s.toSimplexData M v b hb k = 0 := by
      intro k
      apply serreCube_degree_hom_ext A M k
      intro a ha
      change simplexHADegreeDefect A s.toSimplexData M v b hb k
        (eqToHom (congrArg (fun d => (serreCubeComplex A M).X d) ha)
          (serreCubeGenerator A M a)) = 0
      rcases serreCubeGenerator_endpoint_cases M a with ht | ⟨n, m, i, j, ε, he, hi⟩
      · subst a
        exact simplexHADegreeDefect_top_generator_zero A s M v b hb k ha
      · let a' := serreCubeGeneratorConcat (n + 1) (i, serreCubeGeneratorEndpointIndex ε) m j
        let w := simplexHAOrderDimensionCast he v
        have hw : w (Fin.last (n + 1 + m)) < b :=
          lt_of_eq_of_lt (simplexHAOrderDimensionCast_last he v) hb
        have ha' : serreCubeGeneratorDegree (n + 1 + m) a' = k :=
          (serreCubeGeneratorDegree_heq he a a' hi).symm.trans ha
        have hs : ∀ d < n + 1 + m, SimplexHAChainLiftExists A s.toSimplexData d :=
          fun d hd => ih d (by omega)
        have hz := simplexHADegreeDefect_endpoint_concat_zero A s.toSimplexData
          n m i j ε w b hw hs k ha'
        exact (simplexHADegreeDefect_generator_zero_heq A s.toSimplexData he a a' hi v w
          (simplexHAOrderDimensionCast_heq he v).symm b hb hw k ha ha').mpr hz
    exact ⟨simplexHAChainLiftOfDefect A s.toSimplexData M v b hb hd, fun _ => rfl⟩

end SerrePositivity.KST.SConstruction
