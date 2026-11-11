module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePrisms
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinCylinderSimplex

/-!
概要：合成 prism の前面と右 Hom の区間比較に共通する切断座標。
方針：時刻零の頂点を元の番号、時刻一の頂点を追加した最後の番号に送る。
規約：切断前の最大 path 座標を最後以前の最大座標へ移す。
使われ方：合成 prism の射影と既存の区間比較の厳密な同定。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：区間ラベルに従って元の頂点か追加した終点を選ぶ順序写像。
方針：零の逆像が先頭区間であることから単調性を示す。
規約：ラベル零なら元の頂点を保ち、一なら最後の頂点に写す。
使われ方：右 Hom の区間比較の単体座標。 -/
def coherentPrismCut {n : ℕ} (t : Fin (n + 1) →o Fin 2) :
    Fin (n + 1) →o Fin (n + 2) where
  toFun i := if t i = 0 then i.castSucc else Fin.last (n + 1)
  monotone' := by
    intro i j hij
    by_cases hi : t i = 0 <;> by_cases hj : t j = 0
    · simp only [ite_eq_left hi, ite_eq_left hj]
      exact Fin.castSucc_le_castSucc_iff.mpr hij
    · simp only [ite_eq_left hi, ite_eq_right hj]
      exact Fin.le_last _
    · have h := t.monotone hij
      rw [hj] at h
      exact False.elim (hi (le_antisymm h (Fin.zero_le _)))
    · simp only [ite_eq_right hi, ite_eq_right hj, le_refl]

/-- 概要：切断写像は零ラベルの頂点を元の番号に保つ。
方針：定義の零分岐を計算する。
規約：端点移送に使う等式を明示する。
使われ方：右 Hom の非定値部分の正規化。 -/
lemma coherentPrismCut_zero {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    (i : Fin (n + 1)) (hi : t i = 0) : coherentPrismCut t i = i.castSucc := by
  exact ite_eq_left hi

/-- 概要：切断写像は一ラベルの頂点を最後の頂点に送る。
方針：定義の非零分岐を計算する。
規約：ラベルは二値なので非零は一。
使われ方：右 Hom の終点の正規化。 -/
lemma coherentPrismCut_one {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    (i : Fin (n + 1)) (hi : t i ≠ 0) : coherentPrismCut t i = Fin.last (n + 1) := by
  exact ite_eq_right hi

/-- 概要：切断の像の最後以前の最大座標は元の path の切替前の最大座標。
方針：二つの像の所属条件から最大元の両方向の不等式を示す。
規約：path の端点の移送は集合の像の等式で明示する。
使われ方：合成 prism の前面の非定値な Hom の比較。 -/
lemma pathCutMaximum_eq_pathLastMaximum {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0)
    (R : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j))
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j.castSucc))
    (Q : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))))
    (hP : P.I = (fun k : ULift.{u} (Fin (n + 1)) ↦ ULift.up k.down.castSucc) '' R.I)
    (hQ : Q.I = (fun k : ULift.{u} (Fin (n + 1)) ↦
      ULift.up (coherentPrismCut t k.down)) '' R.I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi P = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum Q := by
  apply le_antisymm
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.le_pathLastMaximum
    rw [hQ]
    have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum_spec t hi P
    rw [hP] at hm
    obtain ⟨⟨k⟩, hk, he⟩ := hm.2
    have he' : k = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi P := by
      have hv := congrArg (fun l : ULift.{u} (Fin (n + 2)) ↦ l.down.val) he
      change k.val = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi P).val at hv
      exact Fin.ext hv
    subst k
    exact ⟨ULift.up _, hk, congrArg ULift.up (coherentPrismCut_zero t _ hm.1)⟩
  · have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum_mem Q
    rw [hQ] at hm
    obtain ⟨⟨k⟩, hk, he⟩ := hm
    by_cases ht : t k = 0
    · have he' : k = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum Q := by
        apply Fin.castSucc_inj.mp
        exact (coherentPrismCut_zero t k ht).symm.trans (ULift.ext_iff.mp he)
      rw [← he']
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.le_pathCutMaximum t hi P k ht
      rw [hP]
      exact ⟨ULift.up k, hk, rfl⟩
    · have he' := congrArg (fun k : ULift.{u} (Fin (n + 2)) ↦ k.down.val) he
      change (coherentPrismCut t k).val = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum Q).val at he'
      rw [coherentPrismCut_one t k ht] at he'
      have hlt := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum Q).isLt
      change n + 1 = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum Q).val at he'
      omega

/-- 概要：右 prism の標準単体表示は切断写像を表す。
方針：円柱比較の頂点公式を使い、左右の値を零・一の分岐で計算する。
規約：パラメーターの標準単体は恒等単体。
使われ方：合成 prism の射影の前面と区間比較の同定。 -/
lemma rightMappingSpacePrism_stdSimplex_cut (n : ℕ)
    (t : (Δ[1] : SSet.{u}) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom.app (Opposite.op ⦋n⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism Δ[n]).app (Opposite.op ⦋n⦌)
        (t, SSet.yonedaEquiv (𝟙 Δ[n]))) =
      stdSimplex.objEquiv.symm
        (SimplexCategory.mkHom (coherentPrismCut (stdSimplex.objEquiv t).toOrderHom)) := by
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  let b : (Δ[0] : SSet.{u}) _⦋n⦌ := stdSimplex.objEquiv.symm
    (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0)
  change (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom.app (Opposite.op ⦋n⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap Δ[n] Δ[0]).app (Opposite.op ⦋n⦌)
      ((SSet.yonedaEquiv (𝟙 Δ[n]), t), b))) i).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_stdSimplex_val]
  change (if (t i).val = 0 then i.val else n + 1 + 0) =
    (if (stdSimplex.objEquiv t).toOrderHom i = 0 then i.castSucc else Fin.last (n + 1)).val
  by_cases h : (stdSimplex.objEquiv t).toOrderHom i = 0
  · have h' : (t i).val = 0 := congrArg Fin.val h
    simp only [h, h', ite_true, Fin.val_castSucc]
  · have h' : (t i).val ≠ 0 := fun he ↦ h (Fin.ext he)
    simp only [h, h', ite_false, Nat.add_zero, Fin.val_last]

/-- 概要：前面の切替最大座標と、切断写像後の最後以前の最大座標の射は一致する。
方針：各旗の各 path に最大座標の像の公式を適用する。
規約：始点は零ラベル、終点は一ラベル。
使われ方：合成 prism の射影の非定値 Hom の同定。 -/
lemma coherentPrismCut_maximumMap {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j ≠ 0) :
    (SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n).toOrderHom.uliftMap).map
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩ ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi j.castSucc =
      ((SimplicialThickening.functor (coherentPrismCut t).uliftMap).map
        (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩ ≫
          eqToHom (congrArg₂ (fun a b : Fin (n + 2) ↦ SimplicialCategory.sHom
            (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up b⟩)
            (coherentPrismCut_zero t i hi) (coherentPrismCut_one t j hj))) ≫
              _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro R
  apply stdSimplex.ext
  intro k
  let P := (((SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n).toOrderHom.uliftMap).map
    (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩).app
      (Opposite.op ⦋d⦌) R).obj k
  let T := ((SimplicialThickening.functor (coherentPrismCut t).uliftMap).map
    (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩).app
      (Opposite.op ⦋d⦌) R
  let Q := ((eqToHom (congrArg₂ (fun a b : Fin (n + 2) ↦ SimplicialCategory.sHom
    (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up b⟩)
    (coherentPrismCut_zero t i hi) (coherentPrismCut_one t j hj))).app
      (Opposite.op ⦋d⦌) T).obj k
  have hQ : Q.I = (fun l : ULift.{u} (Fin (n + 1)) ↦
      ULift.up (coherentPrismCut t l.down)) '' (R.obj k).I := by
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.thickeningHom_transport_I
      (congrArg (fun a : Fin (n + 2) ↦
        (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))))
        (coherentPrismCut_zero t i hi))
      (congrArg (fun a : Fin (n + 2) ↦
        (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))))
        (coherentPrismCut_one t j hj)) T k
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi P = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum Q
  exact pathCutMaximum_eq_pathLastMaximum t hi (R.obj k) P Q rfl hQ

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
