module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DegenerateEvaluation

/-!
# 座標を忘れた立方体の旗の消滅

概要：一つでも座標を忘れた立方体の最大旗は退化し、その最上位評価は零である。
方針：忘れた座標が加わる前後の頂点は同じなので、順序 nerve の退化判定を使う。
規約：座標制限は部分型への逆像として定義する。
使われ方：HA 1.3.1.16、Kerodon 2.5.8（Tag 00S0）–2.5.9（Tag 00SC） の AW と shuffle の不要項の消去。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial

/-- 概要：立方体の座標を指定した部分集合へ制限する。
方針：部分型の包含による部分集合の逆像の nerve を取る。
規約：消去した座標は小さい立方体に現れない。
使われ方：Kerodon 2.5.9（Tag 00SC） の左右の因子への座標の射影。 -/
def cubeRestrictionMap {T : Type u} (P : T → Prop) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube {t // P t} :=
  nerveMap (show Monotone (fun U : Set T ↦ {t : {t // P t} | t.val ∈ U}) from
    fun _ _ h _ ht ↦ h ht).functor

/-- 概要：忘れた座標が加わる前後で制限した旗の頂点は一致する。
方針：その番号以外では i 未満と i+1 未満が同値である。
規約：一つの隣接頂点の組の等式。
使われ方：HA 1.3.1.16 の退化した射影旗の検出。 -/
lemma cubeRestrictionMap_flag_repeat {T : Type u} {n : ℕ} (P : T → Prop)
    (e : Fin (n + 1) ≃ T) (i : Fin (n + 1)) (hi : ¬ P (e i)) :
    ((cubeRestrictionMap P).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e)).obj i.castSucc =
      ((cubeRestrictionMap P).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e)).obj i.succ := by
  apply Set.ext
  intro a
  change (e.symm a.val).val < i.val ↔ (e.symm a.val).val < i.val + 1
  have hne : (e.symm a.val).val ≠ i.val := by
    intro h
    have ha : a.val = e i := by
      have he := congrArg e (Fin.ext h)
      simpa using he
    exact hi (ha ▸ a.property)
  omega

variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] {x y : D}

/-- 概要：一つでも座標を忘れた最大旗の最上位評価は零である。
方針：忘れた座標の前後で旗の頂点が一致し、頂点写像が非単射となる。
規約：標準 Hom への射の線形性は要求しない。
使われ方：Kerodon 2.5.8（Tag 00S0） の AW の不要な退化項の消滅。 -/
lemma cubeFlagEvaluation_restriction_zero {T : Type u} {n : ℕ} (P : T → Prop)
    (e : Fin (n + 1) ≃ T) (i : Fin (n + 1)) (hi : ¬ P (e i))
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube {t // P t} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation e (cubeRestrictionMap P ≫ φ) = 0 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval_nerve_zero φ ((cubeRestrictionMap P).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e))
  intro hinj
  exact (ne_of_lt i.castSucc_lt_succ) (hinj (cubeRestrictionMap_flag_repeat P e i hi))

/-- 概要：一座標でも欠く制限を通る立方体評価は零である。
方針：各置換の旗で、欠けた座標の番号を選んで最上位評価を零にする。
規約：次元は正で、欠けた座標を具体的に指定する。
使われ方：HA 1.3.1.16 の退化方向を持つ立方体の基本鎖の消滅。 -/
lemma cubeEvaluation_restriction_zero {T : Type u} {n : ℕ} (P : T → Prop)
    (e : Fin (n + 1) ≃ T) (a : T) (ha : ¬ P a)
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube {t // P t} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation e (cubeRestrictionMap P ≫ φ) = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation
  apply Finset.sum_eq_zero
  intro σ _
  have h : ¬ P ((σ.trans e) ((σ.trans e).symm a)) := by simpa using ha
  rw [cubeFlagEvaluation_restriction_zero P (σ.trans e) _ h φ, smul_zero]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
