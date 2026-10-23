module

public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftPointHomEnriched
public import SerrePositivity.InfinityCategories.F1.Coherent.ReversePointHomAction

/-!
概要：任意のパラメーター付き Kan 値の作用を、反転した豊穣合成そのものへ移す。
方針：元の射を反転して curry し、パラメーターの二重反転を戻して同じ Hom に入れる。
規約：パラメーターの Kan 性は要求しない。係数の同型と反転を明示する。
使われ方：実際の pointed 輸送の合成作用を直接の Kan 作用で記述する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元のパラメーター付き射を、同じ反転した豊穣 Hom のパラメーターへ写す。 -/
def leftPointHomReverseParameter {X Y T : SSet.{u}} (f : X ⊗ T ⟶ Y) :
    (SSet.uliftFunctor.{u + 1, u}).obj T ⟶
      ((SSet.uliftFunctor.{u + 1, u}).obj ((ihom X.op).obj Y.op)).op :=
  (SSet.uliftFunctor.{u + 1, u}).map
    ((SSet.opFunctorCompOpFunctorIso.app T).inv ≫
      SSet.opFunctor.map (curry
        ((HomotopyLimits.oppositeTensorIso X T).inv ≫ SSet.opFunctor.map f))) ≫
    (HomotopyLimits.uliftOppositeIso ((ihom X.op).obj Y.op)).hom

/-- 元の内部 Hom への射で評価を制限しても、同じ反転 Hom のパラメーターを回収する。 -/
lemma leftPointHomReverseParameter_uncurry {X Y H : SSet.{u}}
    (g : H ⟶ (ihom X).obj Y) :
    (SSet.uliftFunctor.{u + 1, u}).map g ≫
      leftPointHomReverseParameter (uncurry (𝟙 ((ihom X).obj Y))) =
        leftPointHomReverseParameter (uncurry g) := by
  have h (A : SSet.{u}) (k : A ⟶ (ihom X).obj Y) :
      curry ((HomotopyLimits.oppositeTensorIso X A).inv ≫
        SSet.opFunctor.map (uncurry k)) =
      SSet.opFunctor.map k ≫ (HomotopyLimits.oppositeInternalHomIso X Y).hom := by
    apply uncurry_injective
    rw [uncurry_curry, oppositeInternalHom_map_uncurry]
    rfl
  rw [leftPointHomReverseParameter, leftPointHomReverseParameter, h, h]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 反転した一点 Hom の直接の作用は、同じパラメーターでの豊穣合成と厳密に一致する。 -/
lemma leftPointHomParameterizedMap_reverseComposition {X Y : KanObject.{u}} {T : SSet.{u}}
    (f : X.obj ⊗ T ⟶ Y.obj) :
    ((HomotopyLimits.uliftOppositeIso
      (SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj X))).hom ⊗ₘ
      leftPointHomReverseParameter f) ≫
      coherentReverseHomComposition (Opposite.op (kanObjectOpFunctor.obj Y))
        (Opposite.op (kanObjectOpFunctor.obj X)) (Opposite.op pointKanObject) =
    (HomotopyLimits.uliftTensorIso
      (SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj X)).op T).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (leftPointHomParameterizedMap f) ≫
      (HomotopyLimits.uliftOppositeIso
        (SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj Y))).hom := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  apply SSet.opObjEquiv.injective
  apply ULift.ext
  apply Functor.HomObj.ext
  funext m α
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- 標準係数の同型を通すと、反転した一点 Hom の作用は元の Kan 値の射となる。 -/
lemma leftPointHomParameterizedMap_coefficient {X Y : KanObject.{u}} {T : SSet.{u}}
    (f : X.obj ⊗ T ⟶ Y.obj) :
    ((pointedSpaceLeftCoefficientIso X).hom ▷ T) ≫ leftPointHomParameterizedMap f =
      f ≫ (pointedSpaceLeftCoefficientIso Y).hom := by
  apply (cancel_mono (pointedSpaceLeftCoefficientIso Y).inv).1
  rw [Category.assoc, leftPointHomParameterizedMap_comparison, ← Category.assoc,
    ← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight, Category.id_comp,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 同じ反転した豊穣合成を標準係数で評価すると、元の Kan 作用を回収する。 -/
lemma leftPointHomReverseComposition_coefficient {X Y : KanObject.{u}} {T : SSet.{u}}
    (f : X.obj ⊗ T ⟶ Y.obj) :
    (((SSet.uliftFunctor.{u + 1, u}).map (pointedSpaceLeftCoefficientIso X).hom ≫
      (HomotopyLimits.uliftOppositeIso
        (SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj X))).hom) ⊗ₘ
      leftPointHomReverseParameter f) ≫
      coherentReverseHomComposition (Opposite.op (kanObjectOpFunctor.obj Y))
        (Opposite.op (kanObjectOpFunctor.obj X)) (Opposite.op pointKanObject) =
    (HomotopyLimits.uliftTensorIso X.obj T).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map f ≫
      (SSet.uliftFunctor.{u + 1, u}).map (pointedSpaceLeftCoefficientIso Y).hom ≫
      (HomotopyLimits.uliftOppositeIso
        (SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj Y))).hom := by
  have h₀ :
      (((SSet.uliftFunctor.{u + 1, u}).map (pointedSpaceLeftCoefficientIso X).hom ≫
        (HomotopyLimits.uliftOppositeIso
          (SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj X))).hom) ⊗ₘ
        leftPointHomReverseParameter f) =
      ((SSet.uliftFunctor.{u + 1, u}).map (pointedSpaceLeftCoefficientIso X).hom ▷
        (SSet.uliftFunctor.{u + 1, u}).obj T) ≫
        ((HomotopyLimits.uliftOppositeIso
          (SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj X))).hom ⊗ₘ
          leftPointHomReverseParameter f) := rfl
  have h₁ :
      ((SSet.uliftFunctor.{u + 1, u}).map (pointedSpaceLeftCoefficientIso X).hom ▷
        (SSet.uliftFunctor.{u + 1, u}).obj T) ≫
        (HomotopyLimits.uliftTensorIso
          (SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj X)).op T).inv =
      (HomotopyLimits.uliftTensorIso X.obj T).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          ((pointedSpaceLeftCoefficientIso X).hom ▷ T) := rfl
  rw [h₀, Category.assoc, leftPointHomParameterizedMap_reverseComposition,
    ← Category.assoc, h₁]
  have h₂ := congrArg (SSet.uliftFunctor.{u + 1, u}).map
    (leftPointHomParameterizedMap_coefficient f)
  have h₃ := congrArg (fun k ↦ (HomotopyLimits.uliftTensorIso X.obj T).inv ≫ k ≫
    (HomotopyLimits.uliftOppositeIso
      (SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj Y))).hom) h₂
  simpa only [Functor.map_comp, Category.assoc] using h₃

end SerrePositivity.InfinityCategories
