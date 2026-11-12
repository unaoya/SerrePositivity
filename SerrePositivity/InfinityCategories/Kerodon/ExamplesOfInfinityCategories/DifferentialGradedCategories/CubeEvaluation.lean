module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeFlags
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplicialCategory

/-!
# 最大旗の符号付き和による立方体の評価

概要：標準 Hom への立方体の射を全ての最大旗で評価し、置換符号で和を取る。
方針：旗の像の最上位成分を取り、立方体の基本鎖の符号付き和を実装する。
規約：番号付け e が向きを固定する。dg nerve の Path には降順の番号付けを使う。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の比較写像の高次成分の候補。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y : D}

/-- 概要：標準 Hom の m 単体の最上位成分を評価する線形写像。
方針：全体集合の次数 1−(m+1)=−m の成分を取る。
規約：零次数も含み、正規化条件は要求しない。
使われ方：HA 1.3.1.16 の立方体の基本鎖の像の評価。 -/
def standardTopEval (x y : D) (m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y m →ₗ[R] GradedHom R x y (-(m : ℤ)) where
  toFun f := f.val.component Finset.univ (-(m : ℤ)) Finset.univ_nonempty (by simp)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 概要：立方体の最大旗の一つの像の最上位成分を取る。
方針：指定した番号付けの旗を標準 Hom へ送り、全体集合で評価する。
規約：台の単体集合の射を使う。
使われ方：Kerodon 2.5.9（Tag 00SC） の立方体の基本鎖の一項。 -/
def cubeFlagEvaluation {T : Type u} {m : ℕ} (e : Fin m ≃ T)
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) : GradedHom R x y (-(m : ℤ)) :=
  standardTopEval (R := R) x y m (φ.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e))

/-- 概要：立方体の基本鎖を標準 Hom で評価する。
方針：全ての座標の置換の最大旗を、置換の符号を係数として足す。
規約：旗の向きは e で固定する。境界公式は別途証明する。
使われ方：HA 1.3.1.16 の coherent nerve から dg nerve への成分。 -/
def cubeEvaluation {T : Type u} {m : ℕ} (e : Fin m ≃ T)
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) : GradedHom R x y (-(m : ℤ)) :=
  ∑ σ : Equiv.Perm (Fin m), (Equiv.Perm.sign σ : ℤ) • cubeFlagEvaluation (σ.trans e) φ

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
