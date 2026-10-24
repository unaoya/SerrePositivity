module

public import SerrePositivity.InfinityCategories.F2.Presentable.IndCardinalChange
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallSolutionCone
public import SerrePositivity.InfinityCategories.F2.Presentable.SolutionGeneratorFactorization
public import SerrePositivity.InfinityCategories.F2.Presentable.ConeVertexPrecomposition

/-!
概要：小さい全解図式に compact 生成対象上の解を頂点とする錐を与える。
方針：極限上の解錐を生成解へ因子化し、同じ辺に沿って全錐を前合成する。
規約：元の全解図式を保持し、始対象性は後続の retract の工程に残す。
使われ方：accessible かつ小極限保存な関手の余表現可能性の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：compact 生成対象上の解を頂点とする小さい全解図式の錐が存在する。
方針：極限保存による解錐の頂点へ、filtered 保存による生成解の辺を入れる。
規約：同じ濃度の生成表示と保存性を要求し、濃度変更を暗黙に行わない。
使われ方：小さい全解の圏から元の圏への錐と retract の構成。 -/
lemma exists_generatorSolutionCone {κ : Cardinal.{u}}
    {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    {i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C}
    (hi : IsKappaCompactGenerating κ i) (F : C ⟶ SpaceInfinity.{u})
    (hC : HasSmallLimits C) (hFa : IsKappaAccessibleFunctor κ F)
    (hFl : PreservesSmallLimits F) :
    ∃ a : A _⦋0⦌, ∃ d : JoinCone (smallSolutionLift i F),
      (leftUnstraighteningProjection F).app (Opposite.op ⦋0⦌) d.vertex =
        i.app (Opposite.op ⦋0⦌) (ULift.up a) := by
  obtain ⟨_, _, d, _⟩ := exists_smallSolutionCone i F hC hFl
  let t : vertexFiber (leftUnstraighteningProjection F)
      ((leftUnstraighteningProjection F).app (Opposite.op ⦋0⦌) d.vertex) _⦋0⦌ :=
    ⟨d.vertex, by rw [PinchedHom.constant_zero]⟩
  obtain ⟨a, w, ⟨e⟩⟩ := exists_generatorSolution_edge hi F hFa _ t
  obtain ⟨d', hd'⟩ := exists_cone_vertex_of_edge d e
  refine ⟨a, d', ?_⟩
  rw [hd']
  simpa only [PinchedHom.constant_zero] using w.property

/-- 概要：accessible な小極限保存関手に対し、生成解を頂点とする全解錐を構成する。
方針：元の圏の濃度を関手の濃度より大きく取り、同じ濃度の構成を適用する。
規約：圏の濃度変更は実証済みの cardinal-change bound を経由する。
使われ方：余表現可能性に必要な小さい全解と生成解の同時選択。 -/
lemma exists_accessibleGeneratorSolutionCone
    {C : SSet.{u + 1}} [Quasicategory C] (F : C ⟶ SpaceInfinity.{u})
    (hCa : IsAccessible C) (hCl : HasSmallLimits C)
    (hFa : IsAccessibleFunctor F) (hFl : PreservesSmallLimits F) :
    ∃ (κ : Cardinal.{u}) (A : SSet.{u}) (hA : Quasicategory A),
      letI := hA
      ∃ i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C,
        κ.IsRegular ∧ IsKappaCompactGenerating κ i ∧ IsKappaAccessibleFunctor κ F ∧
          ∃ a : A _⦋0⦌, ∃ d : JoinCone (smallSolutionLift i F),
            (leftUnstraighteningProjection F).app (Opposite.op ⦋0⦌) d.vertex =
              i.app (Opposite.op ⦋0⦌) (ULift.up a) := by
  obtain ⟨μ, _, hμF⟩ := hFa
  obtain ⟨κ, hμκ, hκC⟩ := hCa.exists_larger μ
  obtain ⟨A, hA, i, hi⟩ := hκC.2.2
  have := hA
  have hκF : IsKappaAccessibleFunctor κ F := hμF.of_le hμκ.le
  exact ⟨κ, A, hA, i, hκC.1, hi, hκF, exists_generatorSolutionCone hi F hCl hκF hFl⟩

end SerrePositivity.InfinityCategories.F2.Presentable
