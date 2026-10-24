module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaSimplicialIndPresentation
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaSiftedGeneration

/-!
概要：任意の P_Σ 対象の simplicial Ind 表示。
方針：元の密度余極限に全単体の bar 表示を適用する。
規約：任意の対象を量化し、全単体的図式とその実現を保持する。
使われ方：filtered 余極限と幾何学的実現による P_Σ の生成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：任意の P_Σ 対象は各項が Ind に属する単体的図式の幾何学的実現である。
方針：元の小さい密度図式を bar で次数ごとの表現可能小余積へ展開する。
規約：元の対象を実現頂点との同型で回収する。
使われ方：HTT 5.5.8 の filtered・geometric な生成表示。 -/
lemma sigmaPresheaf_simplicialIndPresentation (C : SSet.{u}) [Quasicategory C]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    (v : (SigmaPresheafInfinity C) _⦋0⦌) :
    ∃ (G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve SmallSimplexOpposite.{u}) ⟶
        SigmaPresheafInfinity C) (d : JoinCocone G),
      IsColimitCone d ∧ Nonempty (VertexIso d.vertex v) ∧
      ∀ n : SmallSimplexOpposite.{u}, Ind.IsIndVertex Cardinal.aleph0 C
        ((sigmaPresheafInfinityInclusion C).app (Opposite.op ⦋0⦌)
          (G.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex n)))) := by
  obtain ⟨K, p, c, _, _, hv, hc⟩ := sigmaPresheaf_siftedPresentation C hC v
  obtain ⟨G, d, hd, ⟨e⟩, hInd⟩ := sigma_smallDiagram_simplicialIndPresentation hC p c hc
  exact ⟨G, d, hd, ⟨e ≪≫ eqToIso (congrArg HomotopyCategory.mk hv)⟩, hInd⟩

end SerrePositivity.InfinityCategories.F2.Presentable
