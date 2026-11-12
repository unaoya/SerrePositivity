module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.WeightedCoefficientPostcomp

/-!
概要：weighted nerve の境界を最後の面と最後の係数から復元する。
方針：初区間を最後の面へ因子分解し、終点に達する成分は最後の係数で比較する。
規約：全ての面を指定した境界を扱い、Kan 性は使わない。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.4.6（Tag 03BB） の係数の自明 Kan fibration の全境界の充填。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
variable {C : Type u} [Category.{u} C]

/-- 概要：相対境界の各面の底は指定した射列の対応する面。
方針：可換条件を各面に制限し、Yoneda の自然性で単体の等式へ戻す。
規約：面の添字に制限はない。
使われ方：Kerodon 5.3.3.1（Tag 025X） の境界面の係数の型の正規化。 -/
lemma weightedBoundaryFace_base (F : C ⥤ SSet.{u}) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) (a : (boundary (n + 1) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm σ)
    (j : Fin (n + 2)) :
    (SSet.yonedaEquiv (boundary.ι j ≫ a)).1 =
      (SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F).app (Opposite.op ⦋n⦌)
      (SSet.yonedaEquiv (boundary.ι j ≫ a)) =
    (nerve C).map (SimplexCategory.δ j).op σ
  rw [← SSet.yonedaEquiv_comp, Category.assoc, ha, ← Category.assoc, boundary.ι_ι]
  exact (SSet.yonedaEquiv_naturality (SimplexCategory.δ j)
    ((SSet.yonedaEquiv (X := nerve C)).symm σ)).symm.trans
      (congrArg ((nerve C).map (SimplexCategory.δ j).op)
        ((SSet.yonedaEquiv (X := nerve C) (n := ⦋n + 1⦌)).apply_symm_apply σ))

/-- 概要：相対境界の各面を指定した底の上の係数図式として表示する。
方針：各面の底の等式に沿って自然変換を同定する。
規約：等式の証明の選択には依存しない。
使われ方：Kerodon 5.3.3.1（Tag 025X） の境界の係数の比較。 -/
def weightedBoundaryFaceDiagram (F : C ⥤ SSet.{u}) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) (a : (boundary (n + 1) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm σ)
    (j : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶
      (SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ ⋙ F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexDiagram F _ (SSet.yonedaEquiv (boundary.ι j ≫ a))
    (weightedBoundaryFace_base F σ a ha j)

/-- 概要：正規化した境界面の係数から元の面の単体を回収できる。
方針：底を指定した図式の回収の往復則を使う。
規約：ホモトピーを介さない単体の等式。
使われ方：Kerodon 5.3.3.1（Tag 025X） の充填の境界の検証。 -/
lemma weightedBoundaryFaceDiagram_eta (F : C ⥤ SSet.{u}) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) (a : (boundary (n + 1) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm σ)
    (j : Fin (n + 2)) :
    (⟨(SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ,
      weightedBoundaryFaceDiagram F σ a ha j⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n) =
      SSet.yonedaEquiv (boundary.ι j ≫ a) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexDiagram_eta F _ _ _

private lemma boundary_prefix_through_last {n : ℕ} (j : Fin (n + 2))
    (i : Fin (n + 1)) (hi : ((SimplexCategory.δ j).toOrderHom i).val ≤ n) :
    (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n (Nat.le_of_lt_succ i.isLt)) :
        (Δ[i.val] : SSet.{u}) ⟶ Δ[n]) ≫ boundary.ι j =
      stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixThroughLast (SimplexCategory.δ j) i hi) ≫
        boundary.ι (Fin.last (n + 1)) := by
  apply (cancel_mono (boundary (n + 1)).ι).1
  simp only [Category.assoc, boundary.ι_ι]
  change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n _) ≫ stdSimplex.map (SimplexCategory.δ j) =
    stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixThroughLast (SimplexCategory.δ j) i hi) ≫
      stdSimplex.map (SimplexCategory.δ (Fin.last (n + 1)))
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_eq_lastFace]
  exact congrArg stdSimplex.map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixThroughLast_factor (SimplexCategory.δ j) i hi).symm

/-- 概要：最後の面を保つ候補は、境界面の終点を避ける初区間で指定した境界に一致する。
方針：初区間を最後の面へ因子分解し、共通の部分単体の最後の成分を比較する。
規約：i の像が全体の最後の頂点でない場合を扱う。
使われ方：Kerodon 5.3.3.1（Tag 025X） の境界充填の初区間側の一致。 -/
lemma weightedBoundary_prefix_agreement (F : C ⥤ SSet.{u}) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) (a : (boundary (n + 1) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm σ)
    (ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight (n + 1) ⟶ σ ⋙ F)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F (SimplexCategory.δ (Fin.last (n + 1))) ⟨σ, ψ⟩ =
      SSet.yonedaEquiv (boundary.ι (Fin.last (n + 1)) ≫ a))
    (j : Fin (n + 2)) (i : Fin (n + 1))
    (hi : ((SimplexCategory.δ j).toOrderHom i).val ≤ n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F (SimplexCategory.δ j) ⟨σ, ψ⟩).2.app i =
      (weightedBoundaryFaceDiagram F σ a ha j).app i := by
  let β := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n (Nat.le_of_lt_succ i.isLt)
  let γ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixThroughLast (SimplexCategory.δ j) i hi
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F β
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F (SimplexCategory.δ j) ⟨σ, ψ⟩) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F β
      ⟨(SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ,
        weightedBoundaryFaceDiagram F σ a ha j⟩ := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap_comp,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixThroughLast_factor (SimplexCategory.δ j) i hi,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_eq_lastFace, hp,
      weightedBoundaryFaceDiagram_eta]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F).map γ.op
        (SSet.yonedaEquiv (boundary.ι (Fin.last (n + 1)) ≫ a)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F).map β.op (SSet.yonedaEquiv (boundary.ι j ≫ a))
    rw [SSet.yonedaEquiv_naturality, SSet.yonedaEquiv_naturality,
      ← Category.assoc, ← Category.assoc]
    exact congrArg SSet.yonedaEquiv
      (congrArg (fun q ↦ q ≫ a) (boundary_prefix_through_last j i hi).symm)
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex_last_heq F he
  change HEq
    (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction β (Fin.last i.val)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F (SimplexCategory.δ j) ⟨σ, ψ⟩).2.app i)
    (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction β (Fin.last i.val)) ≫
      (weightedBoundaryFaceDiagram F σ a ha j).app i) at ht
  dsimp only [β] at ht
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction_inclusion, CategoryTheory.Functor.map_id, Category.id_comp] at ht
  exact eq_of_heq ht

/-- 概要：最後の面と最後の係数を保つ候補は指定した境界の全ての面を保つ。
方針：終点を避ける成分は初区間で比較し、終点の成分は可逆な輸送を消去して比較する。
規約：一次元の境界も同じ証明に含める。
使われ方：Kerodon 5.3.3.1（Tag 025X） の相対境界充填の全ての面の一致。 -/
lemma weightedBoundary_candidate_face_agreement (F : C ⥤ SSet.{u}) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) (a : (boundary (n + 1) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm σ)
    (ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight (n + 1) ⟶ σ ⋙ F)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F (SimplexCategory.δ (Fin.last (n + 1))) ⟨σ, ψ⟩ =
      SSet.yonedaEquiv (boundary.ι (Fin.last (n + 1)) ≫ a))
    (ht : (boundary (n + 1)).ι ≫ ψ.app (Fin.last (n + 1)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ a (boundary (n + 1)).ι ha)
    (j : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F (SimplexCategory.δ j) ⟨σ, ψ⟩ =
      SSet.yonedaEquiv (boundary.ι j ≫ a) := by
  by_cases hjl : j = Fin.last (n + 1)
  · subst j
    exact hp
  · calc
      _ = ⟨(SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ,
          weightedBoundaryFaceDiagram F σ a ha j⟩ := by
        refine Sigma.ext (by rfl) ?_
        apply heq_of_eq
        apply NatTrans.ext
        funext i
        by_cases hi : (SimplexCategory.δ j).toOrderHom i = Fin.last (n + 1)
        · have hie := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFace_eq_last_of_image_last j i hi
          subst i
          let q := (σ ⋙ F).map
            (homOfLE (Fin.le_last ((SimplexCategory.δ j).toOrderHom (Fin.last n))))
          have : IsIso q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveDiagram_terminal_transport_isIso (σ ⋙ F)
            (SimplexCategory.δ j) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFace_last_of_ne_last j hjl)
          apply (cancel_mono q).1
          calc
            _ = stdSimplex.δ j ≫ ψ.app (Fin.last (n + 1)) :=
              _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveDiagram_terminal_transport (σ ⋙ F) ψ (SimplexCategory.δ j)
            _ = boundary.ι j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ a
                (boundary (n + 1)).ι ha := by
              rw [← boundary.ι_ι j, Category.assoc, ht]
            _ = _ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient_restriction F σ a
              (boundary (n + 1)).ι ha (boundary.ι j) (SimplexCategory.δ j) rfl
              (weightedBoundaryFaceDiagram F σ a ha j)
              ((congrArg SSet.yonedaEquiv.symm
                (weightedBoundaryFaceDiagram_eta F σ a ha j)).trans
                  (SSet.yonedaEquiv.symm_apply_apply _))
        · exact weightedBoundary_prefix_agreement F σ a ha ψ hp j i
            (Nat.le_of_lt_succ (Fin.lt_last_iff_ne_last.mpr hi))
      _ = _ := weightedBoundaryFaceDiagram_eta F σ a ha j

/-- 概要：最後の面と最後の係数を保つ単体は元の境界全体を充填する。
方針：全ての面の単体の等式を Yoneda で射の等式へ戻し、境界の外延性を使う。
規約：係数に Kan 性や充填の仮定は追加しない。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.4.6（Tag 03BB） の最後の係数の相対充填から全空間の充填への復元。 -/
lemma weightedBoundary_reconstruction (F : C ⥤ SSet.{u}) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) (a : (boundary (n + 1) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm σ)
    (ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight (n + 1) ⟶ σ ⋙ F)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F (SimplexCategory.δ (Fin.last (n + 1))) ⟨σ, ψ⟩ =
      SSet.yonedaEquiv (boundary.ι (Fin.last (n + 1)) ≫ a))
    (ht : (boundary (n + 1)).ι ≫ ψ.app (Fin.last (n + 1)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ a (boundary (n + 1)).ι ha) :
    (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm
      (⟨σ, ψ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F (n + 1)) = a := by
  apply boundary.hom_ext
  intro j
  rw [← Category.assoc, boundary.ι_ι]
  exact (SSet.yonedaEquiv_symm_naturality_left (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
      (SimplexCategory.δ j) ⟨σ, ψ⟩).trans
    ((congrArg SSet.yonedaEquiv.symm
      (weightedBoundary_candidate_face_agreement F σ a ha ψ hp ht j)).trans
        (SSet.yonedaEquiv.symm_apply_apply _))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
