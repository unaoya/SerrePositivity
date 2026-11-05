module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.KST.LocalizingInvariants.VerdierRelativeSpanRecovery

/-!
概要：実分母族の連続 Kan 模型から元の完成分数への比較を、単位上で厳密化する。
方針：元の実比較を anodyne 単位に沿って Kan 標的へ延長し、同じ可逆性を反映する。
規約：実族上の合成は元の標準比較の単位像そのもの。
使われ方：指定実境界を変えずに完成分数族を相対的に持ち上げる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open HomotopicalAlgebra SSet.modelCategoryQuillen
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

/-- 元の射を単位上で厳密に回収する Kan 延長のデータ。 -/
def spanRecoveryKanExtensionData {E Y : SSet.{u}} [KanComplex Y] (f : E ⟶ Y) :
    {g : F2.continuousKanReplacement.obj E ⟶ Y //
      F2.continuousKanReplacementUnit.app E ≫ g = f} := by
  have := F2.continuousKanReplacementUnit_anodyne E (terminal.from Y)
    (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)
  have sq : CommSq f (F2.continuousKanReplacementUnit.app E) (terminal.from Y)
      (terminal.from (F2.continuousKanReplacement.obj E)) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

def spanRecoveryKanExtension {E Y : SSet.{u}} [KanComplex Y] (f : E ⟶ Y) :
    F2.continuousKanReplacement.obj E ⟶ Y := (spanRecoveryKanExtensionData f).val

lemma spanRecoveryKanExtension_unit {E Y : SSet.{u}} [KanComplex Y] (f : E ⟶ Y) :
    F2.continuousKanReplacementUnit.app E ≫ spanRecoveryKanExtension f = f :=
  (spanRecoveryKanExtensionData f).property

/-- 単位を保つ延長は、元の anodyne 局所化同型を Kan 同値へ戻す。 -/
lemma spanRecoveryKanExtension_isQCatEquivalence {E Y : SSet.{u}} [KanComplex Y]
    (f : E ⟶ Y) (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) :
    IsQCatEquivalence (spanRecoveryKanExtension f) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have hu : IsIso (Q.map (F2.continuousKanReplacementUnit.app E)) :=
    SSet.anodyneExtensions.Q_inverts _ (F2.continuousKanReplacementUnit_anodyne E)
  have he := congrArg (fun g => Q.map g) (spanRecoveryKanExtension_unit f)
  rw [Q.map_comp] at he
  have hc : IsIso (Q.map (F2.continuousKanReplacementUnit.app E) ≫
      Q.map (spanRecoveryKanExtension f)) := he.symm ▸ hf
  exact isQCatEquivalence_of_anodyneQ_isIso _ ((isIso_comp_left_iff _ _).mp hc)

/-- 実分母族の Kan 模型から、元の完成分数への単位を保つ実比較。 -/
def verdierSpanKanComparison {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) :
    F2.continuousKanReplacement.obj (verdierDenominatorSpanFamily i x y) ⟶
      groupoidCompletion (fixedMarkedSpans B.obj (weakEquivalences i) x y) :=
  spanRecoveryKanExtension (verdierDenominatorSpanCanonicalComparison i x y ≫
    groupoidCompletionMap (fixedMarkedSpans B.obj (weakEquivalences i) x y))

lemma verdierSpanKanComparison_unit {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) :
    F2.continuousKanReplacementUnit.app (verdierDenominatorSpanFamily i x y) ≫
      verdierSpanKanComparison i x y = verdierDenominatorSpanCanonicalComparison i x y ≫
        groupoidCompletionMap (fixedMarkedSpans B.obj (weakEquivalences i) x y) :=
  spanRecoveryKanExtension_unit _

lemma verdierSpanKanComparison_isQCatEquivalence
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) (x y : B.obj _⦋0⦌) :
    IsQCatEquivalence (verdierSpanKanComparison i x y) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have hu : IsIso (Q.map (F2.continuousKanReplacementUnit.app
      (verdierDenominatorSpanFamily i x y))) :=
    SSet.anodyneExtensions.Q_inverts _ (F2.continuousKanReplacementUnit_anodyne _)
  have hf : IsIso (Q.map (verdierDenominatorSpanCanonicalComparison i x y)) :=
    homotopyEquivalence_anodyneQ_isIso _
      (IsQCatEquivalence.isSimplicialHomotopyEquivalence
        (verdierDenominatorSpanCanonicalComparison_isQCatEquivalence h x y))
  have hv := groupoidCompletionUnit_anodyneQ_isIso
    (fixedMarkedSpans B.obj (weakEquivalences i) x y)
  have he := congrArg (fun f => Q.map f) (verdierSpanKanComparison_unit i x y)
  rw [Q.map_comp, Q.map_comp] at he
  have hc : IsIso (Q.map (F2.continuousKanReplacementUnit.app
      (verdierDenominatorSpanFamily i x y)) ≫ Q.map (verdierSpanKanComparison i x y)) :=
    he.symm ▸ inferInstance
  exact isQCatEquivalence_of_anodyneQ_isIso _ ((isIso_comp_left_iff _ _).mp hc)

/-- 元の実分数評価も、Sp-6 s4 と同じ単位比較により局所化後に可逆。 -/
lemma verdierFixedFractionEvaluation_localized_isIso
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) (x y : B.obj _⦋0⦌) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts x y)) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have hu := groupoidCompletionUnit_anodyneQ_isIso
    (fixedMarkedSpans B.obj (weakEquivalences i) x y)
  have hc : IsIso (Q.map
      (fractionMappingComparison q.hom (weakEquivalences i) h.inverts x y)) :=
    homotopyEquivalence_anodyneQ_isIso _ (IsQCatEquivalence.isSimplicialHomotopyEquivalence
      (weakFractionMappingComparison_isQCatEquivalence h x y))
  have he := AnodyneHomotopy.map_homotopy_eq Q SSet.anodyneExtensions.Q_inverts
    (FunctorIso.simplicialHomotopy
      (fractionMappingComparisonIso q.hom (weakEquivalences i) h.inverts x y))
  rw [Q.map_comp] at he
  exact he ▸ inferInstance

/-- 商の写像空間への比較を、元の実分数評価を単位上で厳密に保って延長する。 -/
def verdierSpanKanMappingComparison
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) (x y : B.obj _⦋0⦌) :
    F2.continuousKanReplacement.obj (verdierDenominatorSpanFamily i x y) ⟶
      intervalMappingSpace (q.hom.app (Opposite.op ⦋0⦌) x)
        (q.hom.app (Opposite.op ⦋0⦌) y) :=
  spanRecoveryKanExtension (verdierDenominatorSpanCanonicalComparison i x y ≫
    fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts x y)

lemma verdierSpanKanMappingComparison_unit
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) (x y : B.obj _⦋0⦌) :
    F2.continuousKanReplacementUnit.app (verdierDenominatorSpanFamily i x y) ≫
      verdierSpanKanMappingComparison h x y = verdierDenominatorSpanCanonicalComparison i x y ≫
        fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts x y :=
  spanRecoveryKanExtension_unit _

lemma verdierSpanKanMappingComparison_isQCatEquivalence
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) (x y : B.obj _⦋0⦌) :
    IsQCatEquivalence (verdierSpanKanMappingComparison h x y) := by
  have hf := homotopyEquivalence_anodyneQ_isIso _
    (IsQCatEquivalence.isSimplicialHomotopyEquivalence
      (verdierDenominatorSpanCanonicalComparison_isQCatEquivalence h x y))
  have hv := verdierFixedFractionEvaluation_localized_isIso h x y
  apply spanRecoveryKanExtension_isQCatEquivalence
  rw [AnodyneHomotopy.anodyneQ.map_comp]
  infer_instance

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanRecoveryKanExtension (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanRecoveryKanExtension := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanRecoveryKanExtension

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanRecoveryKanExtensionData (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanRecoveryKanExtensionData := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanRecoveryKanExtensionData

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanRecoveryKanExtension_isQCatEquivalence := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanRecoveryKanExtension_isQCatEquivalence

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanRecoveryKanExtension_unit := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanRecoveryKanExtension_unit

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierFixedFractionEvaluation_localized_isIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierFixedFractionEvaluation_localized_isIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanKanComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanKanComparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanKanComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanKanComparison_isQCatEquivalence := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanKanComparison_isQCatEquivalence

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanKanComparison_unit := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanKanComparison_unit

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanKanMappingComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanKanMappingComparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanKanMappingComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanKanMappingComparison_isQCatEquivalence := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanKanMappingComparison_isQCatEquivalence

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanKanMappingComparison_unit := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanKanMappingComparison_unit

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanRecoveryKanExtensionData._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanRecoveryKanExtensionData._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanRecoveryKanExtensionData._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanRecoveryKanExtensionData._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanRecoveryKanExtensionData._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanRecoveryKanExtensionData._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanRecoveryKanExtensionData._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanRecoveryKanExtensionData._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanRecoveryKanExtensionData._proof_5 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanRecoveryKanExtensionData._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanRecoveryKanExtensionData._proof_6 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanRecoveryKanExtensionData._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanKanComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanKanComparison._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanKanMappingComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanKanMappingComparison._proof_1
