module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.GeometricallyIntegralCompleteProjective
public import SerrePositivity.AlgebraicGeometry.ProjectiveReductionBaseChange
public import SerrePositivity.AlgebraicGeometry.LocalizationCompletionProjectivity
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Algebra
public import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
概要：KST §5、Stacks 05FS の元の剰余の射影性から完備化後の射影性への接続。
方針：既存の完備化の Noether 性と、剰余の射影性の基底変更を完備基底上の判定へ渡す。
規約：CommutativeAlgebra の既証の Noether 性を読み取り専用で利用する。
使われ方：一般自由性と Noether 帰納法から幾何学的整な代数の射影性を得る。
-/

@[expose] public section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：幾何学的整な平坦有限表示代数は、元の剰余が射影的なら完備化した基底上で射影的。
方針：完備化の Noether 性・拡大イデアル進完備性と剰余の射影性の基底変更を組み合わせる。
規約：KST §5、Stacks 05FS、元の基底自体の完備性は要求しない。
使われ方：局所化と完備化の忠実平坦被覆の完備化側。
-/
theorem projective_geometricallyIntegral_completion_baseChange
    (R B : Type u) [CommRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B]
    [Module.Flat R B] [Algebra.FinitePresentation R B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
    (I : Ideal R) [Module.Projective (R ⧸ I) (B ⧸ (I • (⊤ : Submodule R B)))] :
    Module.Projective (AdicCompletion I R) ((AdicCompletion I R) ⊗[R] B) := by
  let C := AdicCompletion I R
  let J := I.map (algebraMap R C)
  let : IsNoetherianRing C := SerrePositivity.isNoetherianRing_adicCompletion R I
  let : IsAdicComplete J C := AdicCompletion.isAdicComplete_self I I.fg_of_isNoetherianRing
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom
      (algebraMap C (C ⊗[R] B)))) := geometricallyIntegral_tensorProjection R B C
  let : Module.Projective (C ⧸ J)
      ((C ⊗[R] B) ⧸ (J • (⊤ : Submodule C (C ⊗[R] B)))) :=
    projective_reduction_baseChange (C := C) (M := B) I
  exact projective_geometricallyIntegral_of_complete_of_projective_reduction C (C ⊗[R] B) J

/--
概要：幾何学的整な平坦有限表示代数は、一つの局所化が自由で対応する剰余が射影的なら射影的。
方針：元の剰余から完備化側の射影性を作り、局所化・完備化の忠実平坦判定を使う。
規約：KST §5、Stacks 05FS の Noether 帰納法で使う帰着。元の非零性はこの帰着には不要。
使われ方：一般自由性と真のイデアルの剰余の射影性を接続する。
-/
theorem projective_geometricallyIntegral_of_free_localization_of_projective_reduction
    (R B : Type u) [CommRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B]
    [Module.Flat R B] [Algebra.FinitePresentation R B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R B)))] (f : R)
    [Module.Free (Localization.Away f) ((Localization.Away f) ⊗[R] B)]
    [Module.Projective (R ⧸ Ideal.span {f})
      (B ⧸ ((Ideal.span {f}) • (⊤ : Submodule R B)))] : Module.Projective R B := by
  let : Module.Projective (AdicCompletion (Ideal.span {f}) R)
      ((AdicCompletion (Ideal.span {f}) R) ⊗[R] B) :=
    projective_geometricallyIntegral_completion_baseChange R B (Ideal.span {f})
  exact projective_of_finiteType_finite_flat_of_localization_completion R B B f

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
