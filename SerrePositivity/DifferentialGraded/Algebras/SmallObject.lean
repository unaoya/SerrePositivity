module

public import SerrePositivity.DifferentialGraded.Algebras.AllColimits
public import SerrePositivity.HomotopicalAlgebra.Complexes.ProjectiveModel
public import Mathlib.CategoryTheory.Presentable.Adjunction

/-!
# dg モノイドの自由生成射の小対象性

概要：同じ球面・円盤上の自由モノイド射は小対象論法を許す。
方針：忘却の filtered 余極限保存から自由対象の有限表示性を移す。
規約：小対象性を新規仮定にせず、実自由随伴から証明する。
使われ方：右転送の二つの関手的分解。
-/

@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DGAlgebra
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DifferentialGraded
variable {R : Type u} [CommRing R]
attribute [local instance] _root_.SerrePositivity.DGAlgebra.hasColimits
attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- 概要：忘却関手の基数ごとの accessible 性。
方針：cardinal-filtered な形の sifted 性と余極限の創出を使う。
規約：係数環の宇宙の図式を使う。
使われ方：自由対象の有限表示性。 -/
lemma forgetIsCardinalAccessible (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    (Mon.forget (Complex R)).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have : IsFiltered J := isFiltered_of_isCardinalFiltered J κ
    have : IsSifted J := IsFiltered.isSifted
    let := _root_.SerrePositivity.DGAlgebra.forgetCreatesSiftedColimits (R := R) J
    infer_instance

attribute [local instance] _root_.SerrePositivity.DGAlgebra.forgetIsCardinalAccessible

/-- 概要：有限表示な複体上の自由モノイドは有限表示。
方針：実自由随伴と忘却の accessible 性を使う。
規約：底の複体にだけ有限表示性を要求する。
使われ方：自由生成射の始域の小対象性。 -/
lemma freeFinitelyPresentable (K : Complex R) [IsFinitelyPresentable.{u} K] :
    IsFinitelyPresentable.{u} (_root_.SerrePositivity.DGAlgebra.freeFunctor.obj K) :=
  _root_.SerrePositivity.DGAlgebra.freeForgetAdjunction.isCardinalPresentable_leftAdjoint_obj Cardinal.aleph0 K

attribute [local instance] _root_.SerrePositivity.DGAlgebra.freeFinitelyPresentable

/-- 概要：有限表示始域を持つ小射族の自由像は小対象論法を許す。
方針：自由始域の有限表示性を正則基数 ℵ₀ の判定へ渡す。
規約：射族の補助宇宙は u で小さい。
使われ方：自由 I・J の両方に適用する。 -/
lemma freeFamily_smallObjectArgument {ι : Type v} [Small.{u} ι] {K L : ι → Complex R}
    (f : ∀ i, K i ⟶ L i) [∀ i, IsFinitelyPresentable.{u} (K i)] :
    ((MorphismProperty.ofHoms f).strictMap _root_.SerrePositivity.DGAlgebra.freeFunctor).HasSmallObjectArgument.{u} := by
  let κ : Cardinal.{u} := Cardinal.aleph0
  let : Fact κ.IsRegular := Cardinal.fact_isRegular_aleph0
  let : Nonempty κ.ord.ToType := Cardinal.nonempty_ord_toType (Fact.out : κ.IsRegular).ne_zero
  let : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot _
  have heq : (MorphismProperty.ofHoms f).strictMap _root_.SerrePositivity.DGAlgebra.freeFunctor =
      MorphismProperty.ofHoms (fun i => _root_.SerrePositivity.DGAlgebra.freeFunctor.map (f i)) := by
    ext X Y g
    constructor
    · rintro ⟨⟨i⟩⟩
      exact ⟨i⟩
    · rintro ⟨i⟩
      exact ⟨⟨i⟩⟩
  have : MorphismProperty.IsCardinalForSmallObjectArgument
      ((MorphismProperty.ofHoms f).strictMap _root_.SerrePositivity.DGAlgebra.freeFunctor) κ := by
    refine { isSmall := ?_, preservesColimit := ?_ }
    · rw [heq]
      infer_instance
    · intro X Y Z W i hi g hg
      cases hi with
      | map hi =>
        cases hi with
        | mk j =>
          exact preservesColimitsOfShape_of_isCardinalPresentable
            (_root_.SerrePositivity.DGAlgebra.freeFunctor.obj (K j)) κ κ.ord.ToType |>.preservesColimit
  exact ⟨κ, inferInstance, inferInstance, inferInstance⟩

/-- 概要：自由球面→円盤の生成射。
方針：元の射影生成族の実自由像。
規約：元の freeFunctor を保持する。
使われ方：dg 代数の cofibration の生成。 -/
def generatingCofibrations : MorphismProperty (Mon (Complex R)) :=
  (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations R).strictMap _root_.SerrePositivity.DGAlgebra.freeFunctor

/-- 概要：自由零→円盤の生成射。
方針：元の射影 trivial 生成族の実自由像。
規約：元の freeFunctor を保持する。
使われ方：dg 代数の trivial cofibration の生成。 -/
def generatingTrivialCofibrations : MorphismProperty (Mon (Complex R)) :=
  (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations R).strictMap _root_.SerrePositivity.DGAlgebra.freeFunctor

/-- 概要：自由 I は小対象論法を許す。
方針：球面の有限表示性を自由射族判定へ代入。
規約：補助宇宙は u。
使われ方：転送の第一の分解。 -/
lemma generatingCofibrations_smallObjectArgument :
    (_root_.SerrePositivity.DGAlgebra.generatingCofibrations (R := R)).HasSmallObjectArgument.{u} :=
  _root_.SerrePositivity.DGAlgebra.freeFamily_smallObjectArgument (complexSphereToDisk R)

/-- 概要：自由 J は小対象論法を許す。
方針：零複体の有限表示性を自由射族判定へ代入。
規約：補助宇宙は u。
使われ方：転送の第二の分解。 -/
lemma generatingTrivialCofibrations_smallObjectArgument :
    (_root_.SerrePositivity.DGAlgebra.generatingTrivialCofibrations (R := R)).HasSmallObjectArgument.{u} :=
  _root_.SerrePositivity.DGAlgebra.freeFamily_smallObjectArgument
    (fun n : ℤ => (0 : (HomologicalComplex.zero : Complex R) ⟶ complexDisk R n))

end SerrePositivity.DGAlgebra
