module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantTransformationPrism

/-!
概要：定値標的への変換の円柱表示の自然性と一意性。
方針：二回の uncurry の自然性と単射性を使う。
規約：部分族の全てのパラメータを保つ。
使われ方：余錐からの比較射をその実際の円柱で検査する。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
variable {K X T U : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}

/-- 概要：変換の円柱表示は追加パラメータの前合成に自然。
方針：区間の uncurry と内部 Hom の uncurry の自然性を続ける。
規約：全次数の射の等式。使われ方：余錐の普遍族の部分族への制限。 -/
lemma constantTransformationPrism_precomp (i : T ⟶ U)
    (a : U ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const z))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantTransformationPrism (i ≫ a) =
      ((K ⊗ (Δ[1] : SSet.{u})) ◁ i) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantTransformationPrism a := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantTransformationPrism, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantTransformationPrism,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, uncurry_natural_left, ← Category.assoc]
  rfl

/-- 概要：変換空間への射は円柱表示で一意に決まる。
方針：結合子を消去し、二回の uncurry の単射性を使う。
規約：標的の充填性は不要。使われ方：比較射・後合成の一致の検査。 -/
lemma constantTransformationPrism_injective : Function.Injective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantTransformationPrism (T := T) (f := f) (z := z)) := by
  intro a b h
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective
  apply uncurry_injective
  exact (cancel_epi (α_ K (Δ[1] : SSet.{u}) T).hom).mp h

/-- 概要：変換の円柱表示から戻すと元の変換の族に一致する。
方針：円柱表示の一意性と curry の計算を使う。
規約：端点の証明の選択には依存しない。使われ方：二つの表示の往復。 -/
lemma constantTransformationCurry_prism
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const z))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantTransformationCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantTransformationPrism a)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantTransformationPrism_zero a) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantTransformationPrism_one a) = a := by
  apply constantTransformationPrism_injective
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantTransformationPrism_curry _ _ _

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
