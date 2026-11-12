module

public import SerrePositivity.CategoryTheory.Enriched.TensorCotensor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-!
概要：SSet の固定 Quillen 類による simplicial model の pushout-product 条件と写像空間の充填。
方針：単射・anodyne とモデル圏の cofibration の pushout-product を使い、随伴で Hom へ移す。
規約：SSet のモデル構造の存在は仮定しない。使われ方：cf 対応圏の混合 Hom と置換射。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits HomotopicalAlgebra SSet
open scoped SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
noncomputable section
variable {C : Type v} [Category.{u} C] [ModelCategory C]

/-- 固定した単射・anodyne による、通常の simplicial pushout-product の三条件。 -/
class FixedSimplicialPushoutProduct (F : SSet.{u} ⥤ C ⥤ C) : Prop where
  cofibration {A B : SSet.{u}} (i : A ⟶ B) [Mono i] {X Y : C} (j : X ⟶ Y)
    [Cofibration j] (sq : F.PushoutObjObj i j) : Cofibration sq.ι
  anodyne {A B : SSet.{u}} (i : A ⟶ B) (hi : anodyneExtensions i)
    {X Y : C} (j : X ⟶ Y) [Cofibration j] (sq : F.PushoutObjObj i j) :
    trivialCofibrations C sq.ι
  trivial {A B : SSet.{u}} (i : A ⟶ B) [Mono i] {X Y : C} (j : X ⟶ Y)
    [Cofibration j] [WeakEquivalence j] (sq : F.PushoutObjObj i j) :
    trivialCofibrations C sq.ι

variable [EnrichedOrdinaryCategory SSet.{u} C]
  (S : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
  [FixedSimplicialPushoutProduct S.tensor]

/-- cofibrant 始域を固定した tensor は、元の全単射を cofibration へ写す。 -/
lemma fixedTensor_mono_cofibration (X : C) [IsCofibrant X]
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i] : Cofibration ((S.tensor.map i).app X) := by
  have : ∀ K : SSet.{u}, (S.tensor.obj K).IsLeftAdjoint :=
    fun K ↦ (S.tensorCotensor.adj K).isLeftAdjoint
  let sq := Functor.PushoutObjObj.ofIsInitialRight S.tensor i (initial.to X) initialIsInitial
  exact FixedSimplicialPushoutProduct.cofibration i (initial.to X) sq

/-- 同じ tensor は元の anodyne 射を trivial cofibration へ写す。 -/
lemma fixedTensor_anodyne_trivialCofibration (X : C) [IsCofibrant X]
    {A B : SSet.{u}} (i : A ⟶ B) (hi : anodyneExtensions i) :
    trivialCofibrations C ((S.tensor.map i).app X) := by
  have : ∀ K : SSet.{u}, (S.tensor.obj K).IsLeftAdjoint :=
    fun K ↦ (S.tensorCotensor.adj K).isLeftAdjoint
  let sq := Functor.PushoutObjObj.ofIsInitialRight S.tensor i (initial.to X) initialIsInitial
  exact FixedSimplicialPushoutProduct.anodyne i hi (initial.to X) sq

include S

/-- cofibrant 始域からの実際の豊穣 Hom は、trivial fibration を trivial Kan 射へ写す。 -/
lemma fixedEnrichedHom_trivialKanFibration (c : C) [IsCofibrant c]
    {Y Z : C} (p : Y ⟶ Z) [Fibration p] [WeakEquivalence p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (eHomWhiskerLeft SSet.{u} c p) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).mpr
  intro n
  have : Cofibration ((S.tensor.flip.obj c).map (boundary n).ι) :=
    fixedTensor_mono_cofibration S c (boundary n).ι
  exact ((S.tensorHom.adj c).hasLiftingProperty_iff (boundary n).ι p).mp inferInstance

/-- cofibrant 始域からの豊穣 Hom は、fibration を固定 Quillen 類の fibration へ写す。 -/
lemma fixedEnrichedHom_fibration (c : C) [IsCofibrant c]
    {Y Z : C} (p : Y ⟶ Z) [Fibration p] :
    Fibration (eHomWhiskerLeft SSet.{u} c p) := by
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  intro A B i hi
  obtain ⟨n, ⟨j⟩⟩ := (by simpa only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff]
    using hi)
  have ht := fixedTensor_anodyne_trivialCofibration S c (horn (n + 1) j).ι
    (anodyneExtensions.horn_ι j)
  have : Cofibration ((S.tensor.flip.obj c).map (horn (n + 1) j).ι) := ⟨ht.1⟩
  have : WeakEquivalence ((S.tensor.flip.obj c).map (horn (n + 1) j).ι) := ⟨ht.2⟩
  exact ((S.tensorHom.adj c).hasLiftingProperty_iff (horn (n + 1) j).ι p).mp inferInstance

/-- 元の cofibrant 始域と fibrant 終域の豊穣写像空間は、固定 Quillen 類で Kan になる。 -/
lemma fixedEnrichedHom_kanComplex (X Y : C) [IsCofibrant X] [IsFibrant Y] :
    KanComplex (X ⟶[SSet.{u}] Y) := by
  let F := (eHomFunctor SSet.{u} C).obj (Opposite.op X)
  have : F.IsRightAdjoint := (S.tensorHom.adj X).isRightAdjoint
  have : Fibration (F.map (terminal.from Y)) := fixedEnrichedHom_fibration S X (terminal.from Y)
  exact (isFibrant_iff_of_isTerminal (F.map (terminal.from Y))
    (terminalIsTerminal.isTerminalObj F (⊤_ C))).mpr inferInstance

/-- 元の trivial cofibration による前合成も、fibrant 終域で trivial Kan fibration となる。 -/
lemma fixedEnrichedHom_sourceTrivialKanFibration {X Z : C} (i : X ⟶ Z)
    [Cofibration i] [WeakEquivalence i] (Y : C) [IsFibrant Y] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (eHomWhiskerRight SSet.{u} i Y) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).mpr
  intro n
  have : ((eHomFunctor SSet.{u} C).obj (Opposite.op X)).IsRightAdjoint :=
    (S.tensorHom.adj X).isRightAdjoint
  have : ((eHomFunctor SSet.{u} C).obj (Opposite.op Z)).IsRightAdjoint :=
    (S.tensorHom.adj Z).isRightAdjoint
  let sq := Functor.PushoutObjObj.ofHasPushout S.tensor (boundary n).ι i
  let sh := Functor.PullbackObjObj.ofIsTerminal (eHomFunctor SSet.{u} C) i
    (terminal.from Y) terminalIsTerminal
  have ht := FixedSimplicialPushoutProduct.trivial (boundary n).ι i sq
  have : Cofibration sq.ι := ⟨ht.1⟩
  have : WeakEquivalence sq.ι := ⟨ht.2⟩
  have : HasLiftingProperty sq.flip.ι (terminal.from Y) := by
    change HasLiftingProperty sq.ι (terminal.from Y)
    infer_instance
  exact (S.tensorHom.hasLiftingProperty_iff sq.flip sh).mp inferInstance

end
end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
