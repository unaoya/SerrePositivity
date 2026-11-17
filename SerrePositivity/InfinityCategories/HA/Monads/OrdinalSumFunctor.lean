module

public import SerrePositivity.InfinityCategories.HA.Monads.EndpointSimplex
public import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal
public import Mathlib.CategoryTheory.Functor.Currying

/-!
概要：walking adjunction の水平合成に使う非空有限順序集合の順序和。
方針：既存の増大単体圏のテンソルを非空な対象へ制限し、両端の包含を計算する。
規約：両因子の射を同時に動かす実関手。端点保存は一方の因子だけに要求する。
使われ方：HA Proposition 4.7.3.3 の全拡張の添字、Riehl–Verity Remark 3.3.8 の水平合成。
Kerodon Remark 6.2.1.4（Tag 02EN）のホモトピー双圏へ移る前の合成。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory

namespace SerrePositivity.InfinityCategories.HA.Monads

open AugmentedSimplexCategory

/-- 概要：非空な有限順序集合の順序和の実双関手。
方針：増大単体圏のテンソルの恒等射・合成則を使う。
規約：対象の長さはm+n+1。使われ方：Riehl–Verity Remark 3.3.8。 -/
def simplexOrdinalSum : SimplexCategory × SimplexCategory ⥤ SimplexCategory where
  obj X := tensorObjOf X.1 X.2
  map f := tensorHomOf f.1 f.2
  map_id X := by
    have h := AugmentedSimplexCategory.tensor_id (WithInitial.of X.1) (WithInitial.of X.2)
    change tensorHomOf (𝟙 X.1) (𝟙 X.2) = 𝟙 _ at h
    exact h
  map_comp f g := by
    have h := AugmentedSimplexCategory.tensorHom_comp_tensorHom
      (WithInitial.incl.map f.1) (WithInitial.incl.map f.2)
      (WithInitial.incl.map g.1) (WithInitial.incl.map g.2)
    change tensorHomOf f.1 f.2 ≫ tensorHomOf g.1 g.2 =
      tensorHomOf (f.1 ≫ g.1) (f.2 ≫ g.2) at h
    exact h.symm

/-- 概要：順序和の左包含は二つの変数に関して自然。
方針：増大単体圏の同じ包含の自然性を制限する。
規約：始域の左因子から比較する。使われ方：Riehl–Verity Remark 3.3.8 の右側合成。 -/
lemma simplexOrdinalSum_inl {x₁ x₂ y₁ y₂ : SimplexCategory}
    (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) :
    inl' x₁ x₂ ≫ tensorHomOf f g = f ≫ inl' y₁ y₂ := by
  exact AugmentedSimplexCategory.inl_comp_tensorHom
    (WithInitial.incl.map f) (WithInitial.incl.map g)

/-- 概要：順序和の右包含は二つの変数に関して自然。
方針：元のテンソルの包含の自然性を使う。規約：右因子は非空。
使われ方：Riehl–Verity Remark 3.3.8 の左側合成。 -/
lemma simplexOrdinalSum_inr {x₁ x₂ y₁ y₂ : SimplexCategory}
    (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) :
    inr' x₁ x₂ ≫ tensorHomOf f g = g ≫ inr' y₁ y₂ := by
  exact AugmentedSimplexCategory.inr_comp_tensorHom
    (WithInitial.incl.map f) (WithInitial.incl.map g)

/-- 概要：順序和の左包含は最小元を保つ。
方針：既存の包含の値の公式を使う。規約：Finの指定された0。
使われ方：Riehl–Verity Remark 3.3.8 の単位からの包含。 -/
lemma simplexOrdinalSum_inl_zero (x y : SimplexCategory) :
    (inl' x y).toOrderHom 0 = 0 := by
  rw [AugmentedSimplexCategory.inl'_eval]
  rfl

/-- 概要：順序和の右包含は最大元を保つ。
方針：既存の値の公式の添字を計算する。規約：右因子の最後の元を全体の最後の元へ送る。
使われ方：Riehl–Verity Remark 3.3.8 の単位からの包含。 -/
lemma simplexOrdinalSum_inr_last (x y : SimplexCategory) :
    (inr' x y).toOrderHom (Fin.last y.len) = Fin.last (tensorObjOf x y).len := by
  rw [AugmentedSimplexCategory.inr'_eval]
  apply Fin.ext
  dsimp
  omega

/-- 概要：左因子の射が最小元を保てば、順序和の射も最小元を保つ。
方針：左包含の自然性を最小元で評価する。
規約：右因子の射に端点保存は要求しない。使われ方：Riehl–Verity Remark 3.3.8。 -/
lemma simplexOrdinalSum_preservesBottom {x₁ x₂ y₁ y₂ : SimplexCategory}
    (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) (hf : simplexPreservesBottom f) :
    simplexPreservesBottom (tensorHomOf f g) := by
  have h := congrArg (fun k : x₁ ⟶ tensorObjOf y₁ y₂ => k.toOrderHom 0)
    (simplexOrdinalSum_inl f g)
  change (tensorHomOf f g).toOrderHom ((inl' x₁ x₂).toOrderHom 0) =
    (inl' y₁ y₂).toOrderHom (f.toOrderHom 0) at h
  rw [simplexOrdinalSum_inl_zero, hf, simplexOrdinalSum_inl_zero] at h
  exact h

/-- 概要：右因子の射が最大元を保てば、順序和の射も最大元を保つ。
方針：右包含の自然性を最後の元で評価する。
規約：左因子の射は任意。使われ方：Riehl–Verity Remark 3.3.8 の混合Homの合成。 -/
lemma simplexOrdinalSum_preservesTop {x₁ x₂ y₁ y₂ : SimplexCategory}
    (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) (hg : simplexPreservesTop g) :
    simplexPreservesTop (tensorHomOf f g) := by
  have h := congrArg (fun k : x₂ ⟶ tensorObjOf y₁ y₂ =>
    k.toOrderHom (Fin.last x₂.len)) (simplexOrdinalSum_inr f g)
  change (tensorHomOf f g).toOrderHom ((inr' x₁ x₂).toOrderHom (Fin.last x₂.len)) =
    (inr' y₁ y₂).toOrderHom (g.toOrderHom (Fin.last x₂.len)) at h
  rw [simplexOrdinalSum_inr_last, hg, simplexOrdinalSum_inr_last] at h
  exact h

end SerrePositivity.InfinityCategories.HA.Monads
