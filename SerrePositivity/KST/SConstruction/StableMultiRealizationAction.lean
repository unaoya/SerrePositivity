module
public import SerrePositivity.KST.SConstruction.DiagonalParameterizedEvaluation
public import SerrePositivity.KST.SConstruction.InternalEnrichedActionLaws
public import SerrePositivity.KST.SConstruction.StableMultiRealizationEnrichedFunctor

/-! # 元の反復実現への完全関手の全作用
概要：元の全反復実現の作用を明示し、各段の元の全作用と同定する。
方針：標準 end の各射影の回収と対角評価を合成する。
規約：全 Kan 入力を保持する。使われ方：全零境界の保存と同じ点つき商への降下。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories LocalizingInvariants

/-- 同じ元の全反復実現の実値を、具体的な既存の模型として明示する。 -/
def stableMultiRealizationValue (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    SSet.{u} :=
  multiDiagonalCoreSConstruction r
    (stableCategoryModel C)

/-- 同じ元の全反復実現に対する、完全関手の全自然同値入力族の実作用。 -/
def stableMultiRealizationAction (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableMultiRealizationValue r C) ⊗
      (C ⟶[SSet.{u}] D) ⟶
        (stableMultiRealizationValue r D) :=
  uncurry ((stableMultiRealizationEnrichedFunctor r).map C D)

/-- 各次数の実現作用は、元の同じ多次数の安定 core の全作用。 -/
lemma stableMultiRealizationAction_app (r : ℕ)
    (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) (n : SimplexCategoryᵒᵖ)
    (x : (stableMultiRealizationValue r C).obj n)
    (p : (C ⟶[SSet.{u}] D).obj n) :
    (stableMultiRealizationAction r C D).app n (x, p) =
      (uncurry (((stableMultiSCoreEnrichedDiagram r).obj (fun _ => n)).map
        C D)).app n (x, p) := by
  have h := congrArg (uncurry (C := SSet.{u}))
    (stableMultiSCoreObjectEnrichedFunctor_projection r C D n)
  exact (simplicialSSetDiagramDiagonal_parameter_app
    ((stableMultiSCoreObjectEnrichedFunctor r).map C D) n x p).trans
      (congrArg (fun q => q.app n (x, p)) h)

/-- 元の 安定入力 豊穣恒等入力は、同じ反復実現の恒等作用。 -/
lemma stableMultiRealizationAction_unit (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (𝟙 (stableMultiRealizationValue r C) ⊗ₘ
      eId SSet.{u} C) ≫ stableMultiRealizationAction r C C =
        (ρ_ (stableMultiRealizationValue r C)).hom :=
  internalEnrichedAction_unit (stableMultiRealizationEnrichedFunctor r) C

/-- 二回の元の実現作用は、同じ 完全関手 合成による作用に厳密に一致。 -/
lemma stableMultiRealizationAction_comp (r : ℕ) (C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableMultiRealizationAction r C D ⊗ₘ
      𝟙 (D ⟶[SSet.{u}] E)) ≫ stableMultiRealizationAction r D E =
      (α_ (stableMultiRealizationValue r C)
        (C ⟶[SSet.{u}] D) (D ⟶[SSet.{u}] E)).hom ≫
          (𝟙 _ ⊗ₘ eComp SSet.{u} C D E) ≫
            stableMultiRealizationAction r C E :=
  internalEnrichedAction_comp (stableMultiRealizationEnrichedFunctor r) C D E

/-- 元の完全射を、同じ通常の安定入力射として保持する。 -/
def stableExactInputMap {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : C ⟶ D) :
    stableCategoryModel C ⟶ stableCategoryModel D :=
  ⟨F.hom, @preservesCofiberData_of_isExactFunctor _ _ F.hom F.isExact⟩

/-- 元の通常完全射では、同じ反復実現射を全作用から回収する。 -/
lemma stableMultiRealizationAction_hom (r : ℕ) {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : C ⟶ D) :
    (𝟙 (stableMultiRealizationValue r C) ⊗ₘ eHomEquiv SSet.{u} F) ≫
        stableMultiRealizationAction r C D =
      (ρ_ (stableMultiRealizationValue r C)).hom ≫
        (multiRealizationFunctor r).map (stableExactInputMap F) :=
  internalEnrichedAction_hom (stableMultiRealizationEnrichedFunctor r) F _
    (stableMultiRealizationEnrichedFunctor_hom r F)

end SerrePositivity.KST.SConstruction
