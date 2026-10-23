module

public import SerrePositivity.InfinityCategories.F1.Weighted.NerveHornPrefixAgreement
public import SerrePositivity.InfinityCategories.F1.Weighted.NerveHornCoefficientFaces

/-!
概要：係数ホーンを充填する weighted nerve の候補は元の左ホーンの全ての面を保つ。
方針：初区間は最後の面との交わりで、最後の成分は可逆な係数輸送の消去で比較する。
規約：左ホーンには最後の面が含まれる。
使われ方：Kerodon §5.3.3、Kan 値 weighted nerve の射影の left fibration 性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：係数ホーンを充填する候補は最後以外の面の最後の成分を保つ。
方針：最後の係数値での等式を計算し、終点を保つ面の可逆な輸送を消去する。
規約：j は最後の面でも欠けた面 k でもない。
使われ方：Kerodon §5.3.3、左ホーンの各面の最後の成分の一致。 -/
lemma weightedNerveHorn_candidate_terminal_agreement {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (ψ : simplexPrefixWeight (n + 1) ⟶ σ ⋙ F)
    (hψ : (horn (n + 1) k).ι ≫ ψ.app (Fin.last (n + 1)) =
      weightedNerveHornLastCoefficient F σ k a ha)
    (j : Fin (n + 2)) (hj : j ≠ k) (hjl : j ≠ Fin.last (n + 1)) :
    (weightedNerveSimplexMap F (SimplexCategory.δ j) ⟨σ, ψ⟩).2.app (Fin.last n) =
      (weightedNerveHornFaceDiagram F σ k a ha j hj).app (Fin.last n) := by
  let q := (σ ⋙ F).map
    (homOfLE (Fin.le_last ((SimplexCategory.δ j).toOrderHom (Fin.last n))))
  have : IsIso q := weightedNerveDiagram_terminal_transport_isIso (σ ⋙ F)
    (SimplexCategory.δ j) (simplexFace_last_of_ne_last j hjl)
  apply (cancel_mono q).1
  calc
    _ = stdSimplex.δ j ≫ ψ.app (Fin.last (n + 1)) :=
      weightedNerveDiagram_terminal_transport (σ ⋙ F) ψ (SimplexCategory.δ j)
    _ = (horn.ι k j hj ≫ (horn (n + 1) k).ι) ≫ ψ.app (Fin.last (n + 1)) :=
      congrArg (fun r ↦ r ≫ ψ.app (Fin.last (n + 1))) (horn.ι_ι k j hj).symm
    _ = horn.ι k j hj ≫ weightedNerveHornLastCoefficient F σ k a ha := by
      rw [Category.assoc, hψ]
    _ = _ := weightedNerveHornLastCoefficient_face F σ k a ha j hj

/-- 概要：最後の面と係数ホーンを保つ候補は左ホーンの指定された全ての面を保つ。
方針：各面の各成分について終点の像か否かで分け、初区間と末端の一致を使う。
規約：全ての次数を扱い、一次ホーンも同じ証明で含める。
使われ方：Kerodon §5.3.3、再構成した weighted nerve の単体が実際のホーン充填となる判定。 -/
lemma weightedNerveHorn_candidate_face_agreement {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C (n + 1))
    (k : Fin (n + 2)) (hk : k ≠ Fin.last (n + 1))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (ψ : simplexPrefixWeight (n + 1) ⟶ σ ⋙ F)
    (hp : weightedNerveSimplexMap F (simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ⟨σ, ψ⟩ =
      SSet.yonedaEquiv (horn.ι k (Fin.last (n + 1)) hk.symm ≫ a))
    (ht : (horn (n + 1) k).ι ≫ ψ.app (Fin.last (n + 1)) =
      weightedNerveHornLastCoefficient F σ k a ha)
    (j : Fin (n + 2)) (hj : j ≠ k) :
    weightedNerveSimplexMap F (SimplexCategory.δ j) ⟨σ, ψ⟩ =
      SSet.yonedaEquiv (horn.ι k j hj ≫ a) := by
  by_cases hjl : j = Fin.last (n + 1)
  · subst j
    rw [← simplexPrefixInclusion_eq_lastFace]
    exact hp
  · calc
      _ = ⟨(SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ,
          weightedNerveHornFaceDiagram F σ k a ha j hj⟩ := by
        refine Sigma.ext (by rfl) ?_
        apply heq_of_eq
        apply NatTrans.ext
        funext i
        by_cases hi : (SimplexCategory.δ j).toOrderHom i = Fin.last (n + 1)
        · have hie := simplexFace_eq_last_of_image_last j i hi
          subst i
          exact weightedNerveHorn_candidate_terminal_agreement F σ k a ha ψ ht j hj hjl
        · have hlt := Fin.lt_last_iff_ne_last.mpr hi
          have hib : ((SimplexCategory.δ j).toOrderHom i).val ≤ n := Nat.le_of_lt_succ hlt
          exact weightedNerveHorn_candidate_prefix_agreement F σ k hk a ha ψ hp j hj i hib
      _ = _ := weightedNerveHornFaceDiagram_eta F σ k a ha j hj

end SerrePositivity.InfinityCategories
