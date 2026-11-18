module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraAllColimits
public import SerrePositivity.HomotopicalAlgebra.Complexes.ProjectiveModel
public import Mathlib.CategoryTheory.Presentable.Adjunction

/-!
模型。文献の定義との比較は後で
# 自由像の生成射の小対象性

概要：Berger–Moerdijk 命題 4.1 の転送に使う自由像の I・J は小対象論法を許す。
方針：忘却の filtered 余極限保存から自由代数の有限表示性を得て、ℵ₀ を使う。
規約：入力の代数の cofibrancy と小対象性を仮定しない。
使われ方：完全な右転送定理の小対象性の入力を供給する。
-/

@[expose] public section

noncomputable section

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A] (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A)

/-- 概要：代数の忘却は各正則基数について accessible（BM §1）。
方針：cardinal-filtered な形の filtered 性と忘却の保存を使う。
規約：補助宇宙は係数環と同じ。
使われ方：自由代数への有限表示性の移送を行う。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget_isCardinalAccessible (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have : IsFiltered J := isFiltered_of_isCardinalFiltered J κ
    infer_instance

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- 概要：有限表示な複体上の自由代数は有限表示（BM §1）。
方針：右随伴の ℵ₀-accessible 性と随伴の Hom 比較を使う。
規約：底の複体の有限表示性だけを入力に取る。
使われ方：自由像の生成射の始域の小対象性を得る。 -/
instance freeAlgebra_finitelyPresentable (K : Complex A) [IsFinitelyPresentable.{u} K] :
    IsFinitelyPresentable.{u} (P.freeAlgebraFunctor.obj K) :=
  P.freeAlgebraAdjunction.isCardinalPresentable_leftAdjoint_obj Cardinal.aleph0 K

/-- 概要：有限表示な始域の小さい射族の自由像は小対象論法を許す（BM 命題 4.1）。
方針：始域の有限表示性を自由随伴で移し、正則基数 ℵ₀ に対する判定を使う。
規約：射族の添字は係数環の宇宙で小さい。
使われ方：自由像の I・J の小対象性を同じ判定で示す。 -/
lemma freeFamily_smallObjectArgument {ι : Type v} [Small.{u} ι] {K L : ι → Complex A}
    (f : ∀ i, K i ⟶ L i) [∀ i, IsFinitelyPresentable.{u} (K i)] :
    ((MorphismProperty.ofHoms f).strictMap P.freeAlgebraFunctor).HasSmallObjectArgument.{u} := by
  letI : HasCoproducts.{u} P.Algebra := fun J => (inferInstance : HasColimitsOfSize.{u, u} P.Algebra).has_colimits_of_shape (Discrete J)
  let κ : Cardinal.{u} := Cardinal.aleph0
  let : Fact κ.IsRegular := Cardinal.fact_isRegular_aleph0
  let : Nonempty κ.ord.ToType := Cardinal.nonempty_ord_toType (Fact.out : κ.IsRegular).ne_zero
  let : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot _
  have heq : (MorphismProperty.ofHoms f).strictMap P.freeAlgebraFunctor =
      MorphismProperty.ofHoms (fun i => P.freeAlgebraFunctor.map (f i)) := by
    ext X Y g
    constructor
    · rintro ⟨⟨i⟩⟩
      exact ⟨i⟩
    · rintro ⟨i⟩
      exact ⟨⟨i⟩⟩
  have : MorphismProperty.IsCardinalForSmallObjectArgument
      ((MorphismProperty.ofHoms f).strictMap P.freeAlgebraFunctor) κ := by
    refine { isSmall := ?_, preservesColimit := ?_ }
    · rw [heq]
      infer_instance
    · intro X Y Z W i hi g hg
      cases hi with
      | map hi =>
        cases hi with
        | mk j =>
          exact preservesColimitsOfShape_of_isCardinalPresentable
            (P.freeAlgebraFunctor.obj (K j)) κ κ.ord.ToType |>.preservesColimit
  exact ⟨κ, inferInstance, inferInstance, inferInstance⟩

/-- 概要：自由像の生成 cofibration は小対象論法を許す（BM 命題 4.1）。
方針：sphere の有限表示性に自由像の射族の判定を適用する。
規約：補助宇宙は u、正則基数は ℵ₀。
使われ方：転送の第一の小対象分解を供給する。 -/
instance freeGeneratingCofibrations_smallObjectArgument :
    MorphismProperty.HasSmallObjectArgument.{u}
      ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).strictMap P.freeAlgebraFunctor) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.freeFamily_smallObjectArgument P (complexSphereToDisk A)

/-- 概要：自由像の生成 trivial cofibration は小対象論法を許す（BM 命題 4.1）。
方針：零複体の有限表示性に自由像の射族の判定を適用する。
規約：入力の代数の cofibrancy を要求しない。
使われ方：転送の第二の小対象分解を供給する。 -/
instance freeGeneratingTrivialCofibrations_smallObjectArgument :
    MorphismProperty.HasSmallObjectArgument.{u}
      ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A).strictMap P.freeAlgebraFunctor) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.freeFamily_smallObjectArgument P
    (fun n : ℤ => (0 : (HomologicalComplex.zero : Complex A) ⟶ complexDisk A n))

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
