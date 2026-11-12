module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeEvaluation

/-!
# 座標の像による立方体の写像

概要：座標の写像を部分集合の像によって立方体の写像にする。
方針：像の単調性の nerve を取り、同値による番号付けの移送を計算する。
規約：二つの座標集合は同じ宇宙に置く。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の削除した立方体の番号付けの比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial

/-- 概要：座標の写像を立方体の写像へ上げる。
方針：部分集合の像は包含を保つので、その関手の nerve を取る。
規約：単射性は要求しない。
使われ方：Kerodon 2.5.9（Tag 00SC） の座標の埋め込みと番号付けの移送。 -/
def cubeImageMap {A B : Type u} (f : A → B) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube B :=
  nerveMap (show Monotone (fun U : Set A ↦ f '' U) from
    fun _ _ h ↦ Set.image_mono h).functor

/-- 概要：座標の同値による旗の像は移送した番号付けの旗である。
方針：像の所属を同値の逆像によって表す。
規約：番号付けの順序を変えずに座標集合だけを替える。
使われ方：HA 1.3.1.16 の削除面の基本鎖の移送。 -/
lemma cubeImageMap_flag {A B : Type u} {m : ℕ} (f : A ≃ B) (e : Fin m ≃ A) :
    (cubeImageMap f).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (e.trans f) := by
  refine CategoryTheory.Functor.ext (fun t ↦ ?_)
  apply Set.ext
  intro b
  change b ∈ f '' {a | (e.symm a).val < t.val} ↔
    (e.symm (f.symm b)).val < t.val
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨f.symm b, h, f.apply_symm_apply b⟩

variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] {x y : D}

/-- 概要：旗の評価は座標同値による移送と可換である。
方針：合成写像の評価と移送した旗の等式を使う。
規約：向きの基準も同じ同値で移送する。
使われ方：Kerodon 2.5.9（Tag 00SC） の座標面の評価の比較。 -/
lemma cubeFlagEvaluation_imageMap {A B : Type u} {m : ℕ} (f : A ≃ B) (e : Fin m ≃ A)
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation e (cubeImageMap f ≫ φ) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation (e.trans f) φ := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) x y m (φ.app _ ((cubeImageMap f).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e))) = _
  rw [cubeImageMap_flag]

/-- 概要：立方体評価は座標同値と番号付けの同時移送に関して不変である。
方針：全置換の和の各旗で移送の式を使う。
規約：番号付けを固定したままの置換不変性は主張しない。
使われ方：HA 1.3.1.16 の削除面を小さい立方体の評価へ戻す。 -/
lemma cubeEvaluation_imageMap {A B : Type u} {m : ℕ} (f : A ≃ B) (e : Fin m ≃ A)
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation e (cubeImageMap f ≫ φ) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation (e.trans f) φ := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation
  apply Finset.sum_congr rfl
  intro σ _
  rw [cubeFlagEvaluation_imageMap]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
