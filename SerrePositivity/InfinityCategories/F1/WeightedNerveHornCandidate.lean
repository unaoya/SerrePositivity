module

public import SerrePositivity.InfinityCategories.F1.WeightedNerveCoefficientRestriction
public import SerrePositivity.InfinityCategories.F1.WeightedNerveHornDiagrams
public import SerrePositivity.InfinityCategories.F1.WeightedNerveLastFace

/-!
概要：相対左ホーンの最後の面を保つ weighted nerve の単体の構成。
方針：最後の面の図式に、最後の係数値で充填した単体を追加する。
規約：他の面の一致は係数の式と面の交わりの比較で後続に確認する。
使われ方：Kerodon §5.3.3、Kan 値 weighted nerve の左ホーン充填の単体の組み立て。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：左ホーンの最後の面の底は指定した射列の初区間。
方針：ホーン面の底の式と、初区間の包含が最後の面であることを組み合わせる。
規約：k≠last により最後の面がホーンに含まれる。
使われ方：Kerodon §5.3.3、左ホーンの初区間の図式の表示を固定する条件。 -/
lemma weightedNerveHornPrefix_base {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (hk : k ≠ Fin.last (n + 1))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ) :
    (SSet.yonedaEquiv (horn.ι k (Fin.last (n + 1)) hk.symm ≫ a)).1 =
      weightedNervePrefixFunctor n ⋙ σ :=
  (weightedNerveHornFace_base F σ k a ha _ hk.symm).trans
    (congrArg (fun q ↦ (SimplexCategory.toCat.map q).toFunctor ⋙ σ)
      (simplexPrefixInclusion_eq_lastFace n).symm)

/-- 概要：左ホーンの最後の面を初区間の重み付き図式として回収する。
方針：最後の面の底を初区間の射列へ同定する。
規約：係数の Kan 性はこの回収には不要。
使われ方：Kerodon §5.3.3、係数充填に最後の単体を追加する前の図式。 -/
def weightedNerveHornPrefixDiagram {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (hk : k ≠ Fin.last (n + 1))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ) :
    simplexPrefixWeight n ⟶ weightedNervePrefixFunctor n ⋙ σ ⋙ F :=
  weightedNerveSimplexDiagram F _
    (SSet.yonedaEquiv (horn.ι k (Fin.last (n + 1)) hk.symm ≫ a))
    (weightedNerveHornPrefix_base F σ k hk a ha)

/-- 概要：回収した初区間の図式の Yoneda 表示は元の左ホーンの最後の面。
方針：指定した底の上で図式を回収する操作の往復則を使う。
規約：底の表示だけを同定し、図式の射を変更しない。
使われ方：Kerodon §5.3.3、係数評価の最後の面を既存の図式に一致させる式。 -/
lemma weightedNerveHornPrefixDiagram_yoneda {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (hk : k ≠ Fin.last (n + 1))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ) :
    SSet.yonedaEquiv.symm
      (⟨weightedNervePrefixFunctor n ⋙ σ, weightedNerveHornPrefixDiagram F σ k hk a ha⟩ :
        weightedNerveSimplex F n) = horn.ι k (Fin.last (n + 1)) hk.symm ≫ a := by
  have he := weightedNerveSimplexDiagram_eta F (weightedNervePrefixFunctor n ⋙ σ)
    (SSet.yonedaEquiv (horn.ι k (Fin.last (n + 1)) hk.symm ≫ a))
    (weightedNerveHornPrefix_base F σ k hk a ha)
  exact (congrArg SSet.yonedaEquiv.symm he).trans (SSet.yonedaEquiv.symm_apply_apply _)

/-- 概要：係数が Kan なら、左ホーンの最後の面を保ち係数ホーンを充填する図式が存在する。
方針：最後の係数値の充填の最後の面を計算し、初区間の図式へその充填を追加する。
規約：全ての他の面との一致は、この存在定理の主張にはまだ含めない。
使われ方：Kerodon §5.3.3、weighted nerve の左ホーン充填の構成段階。 -/
lemma exists_weightedNerveHorn_candidate {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C (n + 1))
    [KanComplex (F.obj (σ.obj (Fin.last (n + 1))))] (k : Fin (n + 2))
    (hk : k ≠ Fin.last (n + 1))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ) :
    ∃ ψ : simplexPrefixWeight (n + 1) ⟶ σ ⋙ F,
      weightedNerveSimplexMap F (simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ⟨σ, ψ⟩ =
        SSet.yonedaEquiv (horn.ι k (Fin.last (n + 1)) hk.symm ≫ a) ∧
      (horn (n + 1) k).ι ≫ ψ.app (Fin.last (n + 1)) =
        weightedNerveHornLastCoefficient F σ k a ha := by
  let τ := weightedNerveHornPrefixDiagram F σ k hk a ha
  let r := horn.ι k (Fin.last (n + 1)) hk.symm
  let α := simplexPrefixInclusion n (n + 1) (Nat.le_succ n)
  have hr : r ≫ (horn (n + 1) k).ι = stdSimplex.map α :=
    (horn.ι_ι k (Fin.last (n + 1)) hk.symm).trans
      (congrArg (fun q ↦ (stdSimplex.map q : (Δ[n] : SSet.{u}) ⟶ Δ[n + 1]))
        (simplexPrefixInclusion_eq_lastFace n).symm)
  obtain ⟨H, hH⟩ := exists_weightedNerveHornLastCoefficient_filler F σ k a ha
  have hb : stdSimplex.map α ≫ H =
      τ.app (Fin.last n) ≫ (σ ⋙ F).map (homOfLE (Fin.le_last (Fin.last n).castSucc)) := by
    calc
      _ = (r ≫ (horn (n + 1) k).ι) ≫ H := congrArg (fun q ↦ q ≫ H) hr.symm
      _ = r ≫ weightedNerveHornLastCoefficient F σ k a ha := by rw [Category.assoc, hH]
      _ = _ := weightedNerveSimplexCoefficient_restriction F σ a (horn (n + 1) k).ι ha r α hr τ
        (weightedNerveHornPrefixDiagram_yoneda F σ k hk a ha)
  let ψ := weightedNerveDiagramSnocOfLastFace (σ ⋙ F) τ H hb
  have hψ : ψ.app (Fin.last (n + 1)) = H :=
    weightedNerveDiagramSnoc_last (σ ⋙ F) τ H
      (weightedNerveDiagram_lastFace_compatible (σ ⋙ F) τ H hb)
  refine ⟨ψ, ?_, ?_⟩
  · have hp : (⟨weightedNervePrefixFunctor n ⋙ σ, τ⟩ : weightedNerveSimplex F n) =
        SSet.yonedaEquiv (r ≫ a) := by
      apply (SSet.yonedaEquiv (X := weightedNerve F) (n := ⦋n⦌)).symm.injective
      exact (weightedNerveHornPrefixDiagram_yoneda F σ k hk a ha).trans
        (SSet.yonedaEquiv.symm_apply_apply _).symm
    exact (weightedNerveSimplexSnoc_lastFace F σ τ H hb).trans hp
  · rw [hψ]
    exact hH

end SerrePositivity.InfinityCategories
