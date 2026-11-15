module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.EInfinity.BarrattEccles.Modules.StrictRawModules
public import SerrePositivity.EInfinity.ProjectiveModel
public import SerrePositivity.DifferentialGraded.Module.TensorFree
public import SerrePositivity.DifferentialGraded.Module.ActionLimits
public import SerrePositivity.HomotopicalAlgebra.Transfer.Right
public import Mathlib.CategoryTheory.Presentable.Adjunction

/-!
# 固定 BE 底上の自由加群生成射と実小対象性

概要：N01 の projective モデル構造に元の自由 I/J を用意する。
方針：既存の自由評価随伴と評価の全余極限保存を再利用する。
規約：モデル構造を入力にしない。まだモデル構造の存在は主張しない。
使われ方：ModelGeneration.rightTransfer の二つの小対象分解。
文献：Keller, On differential graded categories, Theorem 3.2 (1) の生成射の成分。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.HA.Section7_1_1
variable (A : Type u) [CommRing A]

/-- 概要：同じ一対象 dg 圏の代表で自由加群を作る（HA §4.2.4）。
方針：既存の freeAt を唯一点で評価する。
規約：非有界な任意の複体を許す。使われ方：元の I/J の自由像。 -/
abbrev strictRawModuleFree (X : (operad A).Algebra) :
    Complex A ⥤ strictRawModuleCategory A X :=
  freeAt (Opposite.op DGAlgebraPoint.star)

/-- 概要：実自由加群と同じ台の随伴（HA Corollary 4.2.4.4 の成分）。
方針：同じ自由評価随伴を唯一点に適用する。
規約：モデル構造の仮定はない。使われ方：右転送の持ち上げ類の対応。 -/
def strictRawModuleFreeAdjunction (X : (operad A).Algebra) :
    strictRawModuleFree A X ⊣ strictRawModuleUnderlying X :=
  freeEvaluationAdjunction A _ (Opposite.op DGAlgebraPoint.star)

/-- 概要：同じ自由 sphere 境界の生成 I（Keller Theorem 3.2 (1) の構成）。
方針：元の複体の生成射の厳密自由像を使う。
規約：元の dg 加群圏。使われ方：cofibration の生成。 -/
def strictRawModuleGeneratingCofibrations (X : (operad A).Algebra) :
    MorphismProperty (strictRawModuleCategory A X) :=
  (projectiveGeneratingCofibrations A).strictMap (strictRawModuleFree A X)

/-- 概要：同じ自由 disk 零包含の生成 J（Keller Theorem 3.2 (1) の構成）。
方針：元の複体の零から disk への射を自由に移す。
規約：元の dg 加群圏。使われ方：trivial cofibration の生成。 -/
def strictRawModuleGeneratingTrivialCofibrations (X : (operad A).Algebra) :
    MorphismProperty (strictRawModuleCategory A X) :=
  (projectiveGeneratingTrivialCofibrations A).strictMap (strictRawModuleFree A X)

/-- 概要：唯一点の台が同じ元の objectwise 擬同型を検出する。
方針：全ての点が唯一点と等しいことを使う。
規約：モデル構造を仮定しない。使われ方：転送の弱同値類の照合。
文献：Keller, Theorem 3.2 (1) の構成の成分。 -/
lemma strictRawModuleQuasiIso_eq (X : (operad A).Algebra) :
    moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X)) =
      (quasiIso (ModuleCat A) (.up ℤ)).inverseImage (strictRawModuleUnderlying X) := by
  ext M N f
  constructor
  · intro h
    exact h (Opposite.op DGAlgebraPoint.star)
  · intro h x
    have hx : x = Opposite.op DGAlgebraPoint.star := Subsingleton.elim _ _
    subst x
    exact h

/-- 概要：同じ自由 I の右類は台の全射擬同型。
方針：実自由随伴の持ち上げ対応と複体の既存判定を使う。
規約：モデル構造を仮定しない。使われ方：N01 の第一の右類。
文献：Keller, Theorem 3.2 (1) の構成の成分。 -/
lemma strictRawModuleGeneratingCofibrations_rlp (X : (operad A).Algebra) :
    (strictRawModuleGeneratingCofibrations A X).rlp =
      ((projectiveFibrations A) ⊓ quasiIso (ModuleCat A) (.up ℤ)).inverseImage
        (strictRawModuleUnderlying X) := by
  rw [strictRawModuleGeneratingCofibrations,
    ModelGeneration.strictMap_rlp (strictRawModuleFreeAdjunction A X),
    projectiveGeneratingCofibrations_rlp]

/-- 概要：同じ自由 J の右類は台の全整数次数全射。
方針：実自由随伴の持ち上げ対応と複体の既存判定を使う。
規約：モデル構造を仮定しない。使われ方：N01 の第二の右類。
文献：Keller, Theorem 3.2 (1) の構成の成分。 -/
lemma strictRawModuleGeneratingTrivialCofibrations_rlp (X : (operad A).Algebra) :
    (strictRawModuleGeneratingTrivialCofibrations A X).rlp =
      (projectiveFibrations A).inverseImage (strictRawModuleUnderlying X) := by
  rw [strictRawModuleGeneratingTrivialCofibrations,
    ModelGeneration.strictMap_rlp (strictRawModuleFreeAdjunction A X),
    projectiveGeneratingTrivialCofibrations_rlp]

/-- 概要：台の評価の実余極限保存から accessible 性を得る。
方針：moduleEvaluationPreservesColimitsOfSize をそのまま使う。
規約：基礎環と同じ宇宙 u。使われ方：自由生成始域の有限表示性。
文献：Keller, Theorem 3.2 (1) の構成の成分。 -/
lemma strictRawModuleUnderlying_accessible (X : (operad A).Algebra)
    (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    (strictRawModuleUnderlying X).IsCardinalAccessible κ := by
  change (moduleEvaluation A _ (Opposite.op DGAlgebraPoint.star)).IsCardinalAccessible κ
  infer_instance

attribute [local instance] strictRawModuleUnderlying_accessible
  Cardinal.fact_isRegular_aleph0

/-- 概要：有限表示な複体上の実自由加群は有限表示。
方針：自由評価随伴と台の accessible 性を使う。
規約：小対象性は仮定しない。使われ方：同じ生成 I/J の始域。
文献：Keller, Theorem 3.2 (1) の構成の成分。 -/
lemma strictRawModuleFree_finitelyPresentable (X : (operad A).Algebra)
    (K : Complex A) [IsFinitelyPresentable.{u} K] :
    IsFinitelyPresentable.{u} ((strictRawModuleFree A X).obj K) :=
  (strictRawModuleFreeAdjunction A X).isCardinalPresentable_leftAdjoint_obj Cardinal.aleph0 K

attribute [local instance] strictRawModuleFree_finitelyPresentable

/-- 概要：有限表示始域を持つ実自由射族に小対象論法を構成する。
方針：自由始域の有限表示性を ℵ₀ の小対象判定に渡す。
規約：添字は u-small。使われ方：N01 の二つの関手的分解。
文献：Keller, Theorem 3.2 (1) の構成の成分。 -/
lemma strictRawModuleFreeFamily_smallObjectArgument (X : (operad A).Algebra)
    {ι : Type v} [Small.{u} ι] {K L : ι → Complex A}
    (f : ∀ i, K i ⟶ L i) [∀ i, IsFinitelyPresentable.{u} (K i)] :
    ((MorphismProperty.ofHoms f).strictMap (strictRawModuleFree A X)).HasSmallObjectArgument.{u} := by
  let κ : Cardinal.{u} := Cardinal.aleph0
  let : Fact κ.IsRegular := Cardinal.fact_isRegular_aleph0
  let : Nonempty κ.ord.ToType := Cardinal.nonempty_ord_toType (Fact.out : κ.IsRegular).ne_zero
  let : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot _
  have heq : (MorphismProperty.ofHoms f).strictMap (strictRawModuleFree A X) =
      MorphismProperty.ofHoms (fun i => (strictRawModuleFree A X).map (f i)) := by
    ext M N g
    constructor
    · rintro ⟨⟨i⟩⟩
      exact ⟨i⟩
    · rintro ⟨i⟩
      exact ⟨⟨i⟩⟩
  have : MorphismProperty.IsCardinalForSmallObjectArgument
      ((MorphismProperty.ofHoms f).strictMap (strictRawModuleFree A X)) κ := by
    refine { isSmall := ?_, preservesColimit := ?_ }
    · rw [heq]
      infer_instance
    · intro M N Z W i hi g hg
      cases hi with
      | map hi =>
        cases hi with
        | mk j =>
          exact preservesColimitsOfShape_of_isCardinalPresentable
            ((strictRawModuleFree A X).obj (K j)) κ κ.ord.ToType |>.preservesColimit
  exact ⟨κ, inferInstance, inferInstance, inferInstance⟩

/-- 概要：元の自由 I の実小対象性。
方針：既存の球面の有限表示性を自由射族に適用する。
規約：N01 のモデル構造を仮定しない。使われ方：第一の分解。
文献：Keller, Theorem 3.2 (1) の構成の成分。 -/
lemma strictRawModuleGeneratingCofibrations_smallObjectArgument (X : (operad A).Algebra) :
    (strictRawModuleGeneratingCofibrations A X).HasSmallObjectArgument.{u} :=
  strictRawModuleFreeFamily_smallObjectArgument A X (complexSphereToDisk A)

/-- 概要：元の自由 J の実小対象性。
方針：零複体の有限表示性を自由射族に適用する。
規約：N01 のモデル構造を仮定しない。使われ方：第二の分解。
文献：Keller, Theorem 3.2 (1) の構成の成分。 -/
lemma strictRawModuleGeneratingTrivialCofibrations_smallObjectArgument
    (X : (operad A).Algebra) :
    (strictRawModuleGeneratingTrivialCofibrations A X).HasSmallObjectArgument.{u} :=
  strictRawModuleFreeFamily_smallObjectArgument A X
    (fun n : ℤ => (0 : (HomologicalComplex.zero : Complex A) ⟶ complexDisk A n))

attribute [cite HA "4.2.4.4" (partial := component)
  "同じ dg 加群の自由・忘却随伴の成分。モデル構造の存在はこの宣言に含めない。"]
  strictRawModuleFree strictRawModuleFreeAdjunction

end SerrePositivity.EInfinity.BarrattEccles
