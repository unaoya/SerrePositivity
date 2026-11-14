module


public meta import SerrePositivity.Util.Citation
public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.CategoryTheory.SmallObject.Basic

/-!
分割で生成：docstring を書き直すこと
# Cofibrant generation on Mathlib model categories

The auxiliary small-object universe is explicit. `HasSmallObjectArgument`
already includes smallness, required colimits and transfinite compactness via
Mathlib's cardinal criterion. This file does not assume that any arbitrary
set of generators automatically satisfies that criterion.
-/

@[expose] public section

universe w u v

open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison

variable {C : Type u} [Category.{v} C]

section Model

variable [ModelCategory C]

/-- Cofibrant generation is extra structure on the existing model category:
two generating classes, their small-object hypotheses, and the two right-class
equalities. It is not a replacement definition of a model category. -/
class CofibrantlyGenerated (I J : MorphismProperty C) : Prop where
  smallObjectI : I.HasSmallObjectArgument.{w}
  smallObjectJ : J.HasSmallObjectArgument.{w}
  rlp_I : I.rlp = trivialFibrations C
  rlp_J : J.rlp = fibrations C

attribute [instance] CofibrantlyGenerated.smallObjectI
attribute [instance] CofibrantlyGenerated.smallObjectJ
variable (I J : MorphismProperty C) [hgen : CofibrantlyGenerated.{w} I J]

include hgen

lemma cofibrations_eq_generated : cofibrations C = I.rlp.llp := by
  rw [CofibrantlyGenerated.rlp_I (I := I) (J := J), trivialFibrations_llp]

lemma trivialCofibrations_eq_generated : trivialCofibrations C = J.rlp.llp := by
  rw [CofibrantlyGenerated.rlp_J (I := I) (J := J), fibrations_llp]

/-- Cofibrant generation supplies the first functorial model factorization. -/
lemma hasFunctorialFactorization_cofibration_trivialFibration :
    (cofibrations C).HasFunctorialFactorization (trivialFibrations C) := by
  rw [cofibrations_eq_generated I J, ← CofibrantlyGenerated.rlp_I (I := I) (J := J)]
  infer_instance

/-- Cofibrant generation supplies the second functorial model factorization. -/
lemma hasFunctorialFactorization_trivialCofibration_fibration :
    (trivialCofibrations C).HasFunctorialFactorization (fibrations C) := by
  rw [trivialCofibrations_eq_generated I J, ← CofibrantlyGenerated.rlp_J (I := I) (J := J)]
  infer_instance

end Model

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "A.2.6.1" (partial := direction) "仮定：抽象モデル圏 C、Mathlib IsLocallyPresentable C と CofibrantlyGenerated I J（Lean の形式的な可呈示性が強い）。結論：cofibrations=I.rlp.llp、trivial cofibrations=J.rlp.llp、両生成類は small-object argument を持つ。A.1.2 の最小性と合わせ原典の二つの weak saturation generation の方向は一致。原典の四条件による presentable から Mathlib の定義への完全な比較は未供給。"] _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated
attribute [cite HTT "A.2.6.1" (partial := direction) "仮定：抽象モデル圏 C、Mathlib IsLocallyPresentable C と CofibrantlyGenerated I J（Lean の形式的な可呈示性が強い）。結論：cofibrations=I.rlp.llp、trivial cofibrations=J.rlp.llp、両生成類は small-object argument を持つ。A.1.2 の最小性と合わせ原典の二つの weak saturation generation の方向は一致。原典の四条件による presentable から Mathlib の定義への完全な比較は未供給。"] _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.cofibrations_eq_generated
attribute [cite HTT "A.2.6.1" (partial := direction) "仮定：抽象モデル圏 C、Mathlib IsLocallyPresentable C と CofibrantlyGenerated I J（Lean の形式的な可呈示性が強い）。結論：cofibrations=I.rlp.llp、trivial cofibrations=J.rlp.llp、両生成類は small-object argument を持つ。A.1.2 の最小性と合わせ原典の二つの weak saturation generation の方向は一致。原典の四条件による presentable から Mathlib の定義への完全な比較は未供給。"] _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.trivialCofibrations_eq_generated
attribute [cite HTT "A.2.6.8" (partial := stronger-hyp) "仮定：抽象モデル圏 C、Mathlib IsLocallyPresentable C と小さい生成 I,J の CofibrantlyGenerated（Lean の形式的仮定が強い）。結論：元の W の full arrow subcategory と inclusion が accessible、F=J.rlp と F∩W=I.rlp も同じ right-lifting-class theorem により accessible となり、原典の三結論に一致。HTT の可呈示性と生成の定義から入力を得る完全な比較は未供給。"] _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.rlp_I
attribute [cite HTT "A.2.6.8" (partial := stronger-hyp) "仮定：抽象モデル圏 C、Mathlib IsLocallyPresentable C と小さい生成 I,J の CofibrantlyGenerated（Lean の形式的仮定が強い）。結論：元の W の full arrow subcategory と inclusion が accessible、F=J.rlp と F∩W=I.rlp も同じ right-lifting-class theorem により accessible となり、原典の三結論に一致。HTT の可呈示性と生成の定義から入力を得る完全な比較は未供給。"] _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.rlp_J
