module

public import SerrePositivity.InfinityCategories.F1.SimplicialPairCategory
public import SerrePositivity.InfinityCategories.F1.SimplicialOverCategory
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorEnrichedEvaluation
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorActionEvaluation

/-!
概要：底上の始域と left fibration の標的を同時に動かす相対 Hom の豊穣双関手。
方針：始域の射を前合成し、標的の射を後合成する二つの作用を同じパラメーターで評価する。
規約：始域の射影には充填性を要求せず、標的の left fibration 性で値を Kan にする。
使われ方：復元 span のテスト同型を二変数の共同族へ実現する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 相対 Hom に始域と標的の射を同時に作用させる実際の評価。 -/
def simplicialOverTestAction {B : SSet.{u}}
    (X Y : SimplicialPairObject (SimplicialOverObject B)ᵒᵖ (LeftFibrationObject B)) :
    relativeFunctorSpace X.2.val.hom X.1.unop.val.hom ⊗ SimplicialCategory.sHom X Y ⟶
      relativeFunctorSpace Y.2.val.hom Y.1.unop.val.hom :=
  let P := X.1.unop.val
  let R := Y.1.unop.val
  let Q := X.2.val
  let S := Y.2.val
  let H := relativeFunctorSpace Q.hom P.hom
  let A := relativeFunctorSpace P.hom R.hom
  let K := relativeFunctorSpace S.hom Q.hom
  lift
    (lift (snd H (A ⊗ K) ≫ fst A K) (fst H (A ⊗ K)) ≫
      relativeFunctorComposition R P Q)
    (snd H (A ⊗ K) ≫ snd A K) ≫ relativeFunctorComposition R Q S

/-- 二変数の作用は、任意のパラメーター制限後も前後の三つの相対射の合成。 -/
lemma simplicialOverTestAction_apply {B : SSet.{u}}
    (X Y : SimplicialPairObject (SimplicialOverObject B)ᵒᵖ (LeftFibrationObject B))
    {n m : SimplexCategoryᵒᵖ}
    (f : (relativeFunctorSpace X.2.val.hom X.1.unop.val.hom).obj n)
    (a : (relativeFunctorSpace X.1.unop.val.hom Y.1.unop.val.hom).obj n)
    (b : (relativeFunctorSpace Y.2.val.hom X.2.val.hom).obj n)
    (α : n ⟶ m) (x : Y.1.unop.val.left.obj m) :
    (((simplicialOverTestAction X Y).app n (f, a, b)).val.app m α) x =
      (b.val.app m α) ((f.val.app m α) (a.val.app m α x)) := by
  change (((relativeFunctorComposition Y.1.unop.val X.2.val Y.2.val).app n
    ((relativeFunctorComposition Y.1.unop.val X.1.unop.val X.2.val).app n
      (a, f), b)).val.app m α) x = _
  rw [relativeFunctorComposition_apply, relativeFunctorComposition_apply]

/-- 底上の相対 Hom は始域に反変、left fibration の標的に共変な豊穣双関手。 -/
def simplicialOverTestEnriched (B : SSet.{u}) :
    EnrichedFunctor SSet.{u}
      (SimplicialPairObject (SimplicialOverObject B)ᵒᵖ (LeftFibrationObject B)) KanObject.{u} where
  obj X := ⟨relativeFunctorSpace X.2.val.hom X.1.unop.val.hom, inferInstance⟩
  map X Y := curry (simplicialOverTestAction X Y)
  map_id X := by
    apply uncurry_injective
    change uncurry (eId SSet X ≫ curry (simplicialOverTestAction X X)) =
      uncurry (MonoidalClosed.id (relativeFunctorSpace X.2.val.hom X.1.unop.val.hom))
    rw [uncurry_natural_left, uncurry_curry, MonoidalClosed.id_eq, uncurry_curry]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨f, t⟩
    cases t
    let P := X.1.unop.val
    let Q := X.2.val
    change (relativeFunctorComposition P Q Q).app n
      ((relativeFunctorComposition P P Q).app n
        ((relativeFunctorIdentity P).app n PUnit.unit, f),
      (relativeFunctorIdentity Q).app n PUnit.unit) = f
    have h₁ : (relativeFunctorComposition P P Q).app n
        ((relativeFunctorIdentity P).app n PUnit.unit, f) = f :=
      congrArg (fun k ↦ k.app n f) (relativeFunctorIdentity_comp P Q)
    rw [h₁]
    exact congrArg (fun k ↦ k.app n f) (relativeFunctorComposition_id P Q)
  map_comp _X _Y _Z := by
    apply uncurry_injective
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨f, ⟨a, b⟩, ⟨c, d⟩⟩
    apply Subtype.ext
    apply CategoryTheory.Functor.functorHom_ext
    intro m α
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- 生の双関手の第一変数を固定すると、既存の全標的の豊穣評価を厳密に回収する。 -/
lemma simplicialOverTestEnriched_right {B : SSet.{u}} (a : SimplicialOverObject B) :
    (simplicialPairRightInclusion (Opposite.op a) (LeftFibrationObject B)).comp SSet
      (simplicialOverTestEnriched B) = relativeFunctorEnrichedEvaluation a.val := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro q r
  simp only [eqToHom_refl, Category.comp_id]
  apply uncurry_injective
  change uncurry ((simplicialPairRightInclusion (Opposite.op a)
    (LeftFibrationObject B)).map q r ≫
      curry (simplicialOverTestAction (Opposite.op a, q) (Opposite.op a, r))) =
    uncurry (curry (relativeFunctorComposition a.val q.val r.val))
  rw [uncurry_natural_left, uncurry_curry, uncurry_curry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨f, b⟩
  change (relativeFunctorComposition a.val q.val r.val).app n
    ((relativeFunctorComposition a.val a.val q.val).app n
      ((relativeFunctorIdentity a.val).app n PUnit.unit, f), b) = _
  have h : (relativeFunctorComposition a.val a.val q.val).app n
      ((relativeFunctorIdentity a.val).app n PUnit.unit, f) = f :=
    congrArg (fun k ↦ k.app n f) (relativeFunctorIdentity_comp a.val q.val)
  rw [h]
  rfl

/-- 任意の底上の豊穣関手を、テストの反変な始域の変数へ代入する。 -/
def simplicialOverTestSource {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {B : SSet.{u}} (F : EnrichedFunctor SSet.{u} C (SimplicialOverObject B)) :
    EnrichedFunctor SSet.{u}
      (SimplicialPairObject Cᵒᵖ (LeftFibrationObject B))
      (SimplicialPairObject (SimplicialOverObject B)ᵒᵖ (LeftFibrationObject B)) where
  obj X := (Opposite.op (F.obj X.1.unop), X.2)
  map X Y := F.map Y.1.unop X.1.unop ⊗ₘ 𝟙 _
  map_id X := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro t
    apply Prod.ext
    · exact congrArg (fun k ↦ k.app n t) (F.map_id X.1.unop)
    · rfl
  map_comp X Y Z := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
    apply Prod.ext
    · exact congrArg (fun k ↦ k.app n (c, a)) (F.map_comp Z.1.unop Y.1.unop X.1.unop)
    · rfl

/-- 始域を固定した包含は、底上の豊穣関手の代入と厳密に可換。 -/
lemma simplicialOverTestSource_right {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C] {B : SSet.{u}}
    (F : EnrichedFunctor SSet.{u} C (SimplicialOverObject B)) (X : C) :
    (simplicialPairRightInclusion (Opposite.op X) (LeftFibrationObject B)).comp SSet
      (simplicialOverTestSource F) =
    simplicialPairRightInclusion (Opposite.op (F.obj X)) (LeftFibrationObject B) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro q r
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro b
  apply Prod.ext
  · exact congrArg (fun k ↦ k.app n PUnit.unit) (F.map_id X)
  · rfl

/-- 豊穣関手の各値から全標的への相対 Hom を、二変数の豊穣関手に束ねる。 -/
def simplicialOverTestBifunctor {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {B : SSet.{u}} (F : EnrichedFunctor SSet.{u} C (SimplicialOverObject B)) :
    EnrichedFunctor SSet.{u} (SimplicialPairObject Cᵒᵖ (LeftFibrationObject B)) KanObject.{u} :=
  (simplicialOverTestSource F).comp SSet (simplicialOverTestEnriched B)

/-- 第一変数を固定した双関手は、既存の相対 Hom の豊穣評価そのもの。 -/
lemma simplicialOverTestBifunctor_right {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C] {B : SSet.{u}}
    (F : EnrichedFunctor SSet.{u} C (SimplicialOverObject B)) (X : C) :
    (simplicialPairRightInclusion (Opposite.op X) (LeftFibrationObject B)).comp SSet
      (simplicialOverTestBifunctor F) = relativeFunctorEnrichedEvaluation (F.obj X).val := by
  change ((simplicialPairRightInclusion (Opposite.op X) (LeftFibrationObject B)).comp SSet
    (simplicialOverTestSource F)).comp SSet (simplicialOverTestEnriched B) = _
  rw [simplicialOverTestSource_right, simplicialOverTestEnriched_right]

end SerrePositivity.InfinityCategories
