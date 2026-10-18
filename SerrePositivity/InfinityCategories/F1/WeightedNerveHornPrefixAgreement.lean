module

public import SerrePositivity.InfinityCategories.F1.WeightedNerveFaceGeometry
public import SerrePositivity.InfinityCategories.F1.WeightedNerveHornCandidate
public import SerrePositivity.InfinityCategories.F1.WeightedNerveTerminalTransport

/-!
概要：最後の面を保つ候補は、他の面の最後の頂点を避ける全ての成分で元のホーンに一致する。
方針：面の初区間を最後の面へ因子分解し、ホーン内の交わりでの一致から成分を回収する。
規約：候補の係数充填の条件はこの一致には使わない。
使われ方：Kerodon §5.3.3、weighted nerve の左ホーン充填の初区間側の検査。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：最後の面を保つ候補の面は、終点を避ける初区間の成分で元のホーン面と一致する。
方針：初区間を最後の面へ移し、二通りの制限の単体の等式の最後の成分を比較する。
規約：i の像が全体の最後の頂点でない場合を扱う。
使われ方：Kerodon §5.3.3、全てのホーン面の自然変換の成分の一致。 -/
lemma weightedNerveHorn_candidate_prefix_agreement {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C (n + 1))
    (k : Fin (n + 2)) (hk : k ≠ Fin.last (n + 1))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (ψ : simplexPrefixWeight (n + 1) ⟶ σ ⋙ F)
    (hψ : weightedNerveSimplexMap F (simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ⟨σ, ψ⟩ =
      SSet.yonedaEquiv (horn.ι k (Fin.last (n + 1)) hk.symm ≫ a))
    (j : Fin (n + 2)) (hj : j ≠ k) (i : Fin (n + 1))
    (hi : ((SimplexCategory.δ j).toOrderHom i).val ≤ n) :
    (weightedNerveSimplexMap F (SimplexCategory.δ j) ⟨σ, ψ⟩).2.app i =
      (weightedNerveHornFaceDiagram F σ k a ha j hj).app i := by
  let β := simplexPrefixInclusion i.val n (Nat.le_of_lt_succ i.isLt)
  let γ := simplexPrefixThroughLast (SimplexCategory.δ j) i hi
  let s : weightedNerveSimplex F (n + 1) := ⟨σ, ψ⟩
  have hov := weightedNerveHornFaceDiagram_overlap F σ k a ha j (Fin.last (n + 1))
    hj hk.symm β γ (horn_face_prefix_through_last k hk j hj i hi)
  rw [weightedNerveHornFaceDiagram_eta F σ k a ha (Fin.last (n + 1)) hk.symm] at hov
  have he : weightedNerveSimplexMap F β (weightedNerveSimplexMap F (SimplexCategory.δ j) s) =
      weightedNerveSimplexMap F β
        ⟨(SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ,
          weightedNerveHornFaceDiagram F σ k a ha j hj⟩ := by
    calc
      _ = weightedNerveSimplexMap F (β ≫ SimplexCategory.δ j) s :=
        weightedNerveSimplexMap_comp F β (SimplexCategory.δ j) s
      _ = weightedNerveSimplexMap F
          (γ ≫ simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) s :=
        congrArg (fun q ↦ weightedNerveSimplexMap F q s)
          (simplexPrefixThroughLast_factor (SimplexCategory.δ j) i hi).symm
      _ = weightedNerveSimplexMap F γ (weightedNerveSimplexMap F
          (simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) s) :=
        (weightedNerveSimplexMap_comp F γ _ s).symm
      _ = weightedNerveSimplexMap F γ
          (SSet.yonedaEquiv (horn.ι k (Fin.last (n + 1)) hk.symm ≫ a)) :=
        congrArg (weightedNerveSimplexMap F γ) hψ
      _ = _ := hov.symm
  have ht := weightedNerveSimplex_last_heq F he
  change HEq
    (stdSimplex.map (simplexPrefixRestriction β (Fin.last i.val)) ≫
      (weightedNerveSimplexMap F (SimplexCategory.δ j) ⟨σ, ψ⟩).2.app i)
    (stdSimplex.map (simplexPrefixRestriction β (Fin.last i.val)) ≫
      (weightedNerveHornFaceDiagram F σ k a ha j hj).app i) at ht
  dsimp only [β] at ht
  rw [simplexPrefixRestriction_inclusion, CategoryTheory.Functor.map_id, Category.id_comp] at ht
  exact eq_of_heq ht

end SerrePositivity.InfinityCategories
