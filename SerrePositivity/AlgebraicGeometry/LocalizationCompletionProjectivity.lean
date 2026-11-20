module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.LocalizationCompletionCover
public import SerrePositivity.AlgebraicGeometry.ProductRingBaseChangeProjective
public import SerrePositivity.AlgebraicGeometry.CountableProjectiveFaithfullyFlatDescent

/-!
概要：KST §5、Stacks 05FS の射影性の局所化と主イデアル進完備化への帰着。
方針：二つの基底変更の射影性を積環にまとめ、構成した忠実平坦被覆で降下する。
規約：元の加群は Noether 基底上で可算生成かつ平坦とする。
使われ方：一般の幾何学的整な平坦有限型代数に対する Noether 帰納法。
-/

@[expose] public section
universe u
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：可算生成平坦加群の射影性は、一つの局所化と同じ元の主イデアル進完備化で確認できる。
方針：二因子の射影性から積環上の射影性を作り、忠実平坦降下を使う。
規約：KST §5、Stacks 05FS、元の非零性・正則性はこの判定に不要。
使われ方：一般自由性と剰余の帰納仮定による代数の射影性の存在。
-/
theorem projective_of_countable_flat_of_localization_completion
    {R M : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    (f : R) (hcount : HasCountableGeneratingSet R M)
    [Module.Projective (Localization.Away f) ((Localization.Away f) ⊗[R] M)]
    [Module.Projective (AdicCompletion (Ideal.span {f}) R)
      ((AdicCompletion (Ideal.span {f}) R) ⊗[R] M)] : Module.Projective R M := by
  let T := Localization.Away f × AdicCompletion (Ideal.span {f}) R
  let : Module.FaithfullyFlat R T := faithfullyFlat_localization_completion_product f
  let : Module.Projective T (T ⊗[R] M) := projective_baseChange_product_of_factors
    R (Localization.Away f) (AdicCompletion (Ideal.span {f}) R) M
  exact projective_of_countable_flat_of_faithfullyFlat R T M hcount

/--
概要：有限型代数上有限な平坦加群の射影性は、局所化と同じ元の主イデアル進完備化で確認できる。
方針：有限型の可算生成性を構成済みの局所化・完備化による判定へ渡す。
規約：KST §5、Stacks 05FS、加群は基礎環上で有限とは限らない。
使われ方：幾何学的整な代数そのものの射影性への適用。
-/
theorem projective_of_finiteType_finite_flat_of_localization_completion
    (R B M : Type u) [CommRing R] [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]
    [Module.Finite B M] [Module.Flat R M] (f : R)
    [Module.Projective (Localization.Away f) ((Localization.Away f) ⊗[R] M)]
    [Module.Projective (AdicCompletion (Ideal.span {f}) R)
      ((AdicCompletion (Ideal.span {f}) R) ⊗[R] M)] : Module.Projective R M :=
  projective_of_countable_flat_of_localization_completion f
    (hasCountableGeneratingSet_of_finiteType_finite R B M)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
