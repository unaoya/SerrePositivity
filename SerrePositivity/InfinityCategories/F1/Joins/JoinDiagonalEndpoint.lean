module

public import SerrePositivity.InfinityCategories.F1.Joins.JoinDiagonal
public import SerrePositivity.InfinityCategories.Core.JoinCylinderSimplex
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
概要：join の区間付き対角に沿う右包含の逆像。
方針：切断が零であることから区間の単体が終端に定値であることを示す。
規約：係数の単体集合に quasicategory 性を要求しない。
使われ方：Kerodon Example 5.2.3.4、Proposition 5.2.4.5 の空の始域の基底。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：区間付き対角の単体の切断は区間の零の逆像の大きさ。
方針：対角円柱と通常の join の円柱比較の次数ごとの式を使う。
規約：n は単体の次数。
使われ方：Kerodon Construction 5.2.3.1、端点の逆像の切断判定。 -/
lemma joinDiagonal_app_cut (Y : SSet.{u}) (n : ℕ)
    (t : (Δ[1] : SSet.{u}) _⦋n⦌) (a : Y _⦋n⦌) :
    ((joinDiagonal Y).app (Opposite.op ⦋n⦌) (t, a)).1.val =
      Join.pullCut (stdSimplex.objEquiv t).toOrderHom 1 := by
  change ((joinCylinderMap Y Y).app (Opposite.op ⦋n⦌) ((a, t), a)).1.val = _
  rw [joinCylinderMap_app]
  rfl

/-- 概要：対角の像が右包含に入る単体は終端包含から来る。
方針：切断零から時刻が全頂点で一となり、右包含の単射性で係数を戻す。
規約：等式は同じ次数 n の単体の等式。
使われ方：Kerodon Example 5.2.3.4、右因子の逆像の計算。 -/
lemma joinDiagonal_eq_inr_iff (Y : SSet.{u}) (n : ℕ)
    (z : ((Δ[1] : SSet.{u}) ⊗ Y) _⦋n⦌) (b : Y _⦋n⦌) :
    (joinDiagonal Y).app (Opposite.op ⦋n⦌) z =
        (joinInr Y Y).app (Opposite.op ⦋n⦌) b ↔
      z = (prismEndpoint 1 Y).app (Opposite.op ⦋n⦌) b := by
  constructor
  · rcases z with ⟨t, a⟩
    intro h
    have hc : Join.pullCut (stdSimplex.objEquiv t).toOrderHom 1 = 0 := by
      rw [← joinDiagonal_app_cut Y n t a]
      exact congrArg (fun x : Join.Simplex Y Y n ↦ x.1.val) h
    have ht : t = ((prismEndpoint 1 Y).app (Opposite.op ⦋n⦌) a).1 := by
      apply stdSimplex.ext
      intro i
      apply Fin.ext
      have hi : ¬ (t i).val < 1 := by
        intro hi
        have he := (Join.lt_pullCut_iff (stdSimplex.objEquiv t).toOrderHom 1 i).mpr hi
        rw [hc] at he
        omega
      change (t i).val = 1
      have := (t i).isLt
      omega
    have hz : (t, a) = (prismEndpoint 1 Y).app (Opposite.op ⦋n⦌) a :=
      Prod.ext ht rfl
    have he : (joinDiagonal Y).app (Opposite.op ⦋n⦌)
        ((prismEndpoint 1 Y).app (Opposite.op ⦋n⦌) a) =
        (joinInr Y Y).app (Opposite.op ⦋n⦌) a :=
      congrArg (fun f : Y ⟶ join Y Y ↦ f.app (Opposite.op ⦋n⦌) a)
        (prismEndpoint_one_joinDiagonal Y)
    rw [← hz] at he
    have hab : a = b := (mono_iff_injective ((joinInr Y Y).app _)).mp inferInstance
      (he.symm.trans h)
    simpa only [hab] using hz
  · intro h
    have he : (joinDiagonal Y).app (Opposite.op ⦋n⦌)
        ((prismEndpoint 1 Y).app (Opposite.op ⦋n⦌) b) =
        (joinInr Y Y).app (Opposite.op ⦋n⦌) b :=
      congrArg (fun f : Y ⟶ join Y Y ↦ f.app (Opposite.op ⦋n⦌) b)
        (prismEndpoint_one_joinDiagonal Y)
    exact (congrArg (fun z ↦ (joinDiagonal Y).app (Opposite.op ⦋n⦌) z) h).trans he


/-- 概要：join の右包含を区間付き対角で引き戻すと prism の終端包含になる。
方針：各次数で型の pullback の元による判定を適用する。
規約：左の縦射は Y の恒等射。
使われ方：Kerodon Example 5.2.3.4、relative join の空の始域の同型性。 -/
lemma isPullback_joinDiagonal_inr (Y : SSet.{u}) :
    IsPullback (prismEndpoint 1 Y) (𝟙 Y) (joinDiagonal Y) (joinInr Y Y) := by
  apply IsPullback.of_forall_isPullback_app
  rintro ⟨⟨n⟩⟩
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg (fun f : Y ⟶ join Y Y ↦ f.app (Opposite.op ⦋n⦌))
      ((prismEndpoint_one_joinDiagonal Y).trans (Category.id_comp _).symm)
  · intro x y h
    exact h.2
  · intro z b h
    exact ⟨b, ((joinDiagonal_eq_inr_iff Y n z b).mp h).symm, rfl⟩

end SerrePositivity.InfinityCategories
