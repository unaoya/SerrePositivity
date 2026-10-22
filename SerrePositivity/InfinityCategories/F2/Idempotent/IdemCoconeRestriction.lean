module

public import SerrePositivity.InfinityCategories.F2.Idempotent.IdemCofinality
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightMapMono
public import SerrePositivity.InfinityCategories.F1B.CofinalAnodyneRecognition
public import SerrePositivity.InfinityCategories.Stable.ColimitRestriction

/-!
概要：元の冪等包含への余錐制限は自明 Kan で、同じ余錐の余極限性を保ち反映する。
方針：元の対象と射の単射性を使い、Quillen A の結論を right anodyne 性へ移す。
規約：指定した元の包含と余錐そのものを扱い、余極限の存在を入力に仮定しない。
使われ方：HTT 4.4.5.12 の元の強い分裂からの余錐の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の冪等包含は、元の対象と全射を区別する単射。 -/
instance idemInclusion_mono : Mono idemInclusion.{u} := by
  have : walkingInclusion.{u}.Faithful :=
    inferInstanceAs (CategoryTheory.Idempotents.toKaroubi WalkingIdem.{u}).Faithful
  exact HomotopyLimits.nerveMap_mono_of_faithful walkingInclusion
    (fun _ _ h ↦ congrArg CategoryTheory.Idempotents.Karoubi.X h)

/-- 元の冪等包含そのものは right anodyne。 -/
lemma idemInclusion_rightAnodyne : rightAnodyneExtensions idemInclusion.{u} :=
  idemInclusion_isRightCofinal.rightAnodyneExtensions

/-- 元の全強分裂図式に沿った余錐を元の Idem へ制限する射は自明 Kan。 -/
lemma idemCoconeRestriction_trivialKanFibration {X : SSet.{u}} [Quasicategory X]
    (F : SplitShape ⟶ X) : TrivialKanFibration (sliceUnderRestrict F idemInclusion) :=
  sliceUnderRestrict_trivialKanFibration F idemInclusion idemInclusion_rightAnodyne

/-- 元の全強分裂図式の指定余錐の普遍性は、元の Idem への制限で判定できる。 -/
lemma idemCocone_isColimit_iff_restrict {X : SSet.{u}} [Quasicategory X]
    {F : SplitShape ⟶ X} (c : JoinCocone F) :
    IsColimitCone c ↔ IsColimitCone (c.restrict idemInclusion) :=
  isColimitCone_iff_restrict_of_rightAnodyne c idemInclusion idemInclusion_rightAnodyne

end SerrePositivity.InfinityCategories.F2.Idempotent
