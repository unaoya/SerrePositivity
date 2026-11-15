module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedFunctor
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseSSetMaps

/-!
概要：同じ単体集合値図式をAsSmallとULiftで持ち上げ、同じテンソルを比較する。
方針：指定downの前合成と値のULiftの全忠実性を合わせ、各値の直積の同型を束ねる。
規約：IS-W2 R02〜R03の既存の係数宇宙移送の法則。元の添字射を保つ。
使われ方：同じBK切断空間全体の宇宙変更と指定点の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open CategoryTheory Limits SSet MonoidalCategory
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
variable (I : Type u) [SmallCategory I]

/-- 元の全図式の指定downと同じULiftによる持ち上げ。 -/
def weightedDiagramUniverse : (I ⥤ SSet.{u}) ⥤ (AsSmall.{v} I ⥤ SSet.{max u v}) :=
  (Functor.whiskeringLeft (AsSmall.{v} I) I SSet.{u}).obj AsSmall.down ⋙
    (Functor.whiskeringRight (AsSmall.{v} I) SSet.{u} SSet.{max u v}).obj SSet.uliftFunctor.{max u v,u}

/-- 同じ図式の宇宙変更は全忠実。 -/
instance weightedDiagramUniverse_full : (weightedDiagramUniverse.{u,v} I).Full := by
  letI universePreFull :
      ((Functor.whiskeringLeft (AsSmall.{v} I) I SSet.{u}).obj AsSmall.down).Full :=
    show (((AsSmall.equiv : I ≌ AsSmall.{v} I).congrLeft (E := SSet.{u})).functor).Full from
      inferInstance
  dsimp [weightedDiagramUniverse]
  infer_instance

/-- 同じ図式の宇宙変更は忠実。 -/
instance weightedDiagramUniverse_faithful : (weightedDiagramUniverse.{u,v} I).Faithful := by
  letI universePreFaithful :
      ((Functor.whiskeringLeft (AsSmall.{v} I) I SSet.{u}).obj AsSmall.down).Faithful :=
    show (((AsSmall.equiv : I ≌ AsSmall.{v} I).congrLeft (E := SSet.{u})).functor).Faithful from
      inferInstance
  dsimp [weightedDiagramUniverse]
  infer_instance

/-- 同じ重みと同じ小さいパラメーターのテンソルを宇宙変更する指定同型。 -/
def weightedDiagramUniverseTensorIso (W : I ⥤ SSet.{u}) (A : SSet.{u}) :
    (weightedDiagramUniverse.{u,v} I).obj (W ⊗ (Functor.const I).obj A) ≅
      (weightedDiagramUniverse.{u,v} I).obj W ⊗
        (Functor.const (AsSmall.{v} I)).obj ((SSet.uliftFunctor.{max u v,u}).obj A) :=
  NatIso.ofComponents (fun i => uliftTensorIso.{u,max u v} (W.obj (AsSmall.down.obj i)) A) (by
    intro i j f
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨w, a⟩
    rfl)

/-- 同じテンソルの指定同型の逆は、元の全パラメーター射で自然。 -/
@[reassoc] theorem weightedDiagramUniverseTensorIso_inv_parameter (W : I ⥤ SSet.{u})
    {A B : SSet.{u}} (f : A ⟶ B) :
    ((weightedDiagramUniverse.{u,v} I).obj W ◁
      (Functor.const (AsSmall.{v} I)).map ((SSet.uliftFunctor.{max u v,u}).map f)) ≫
        (weightedDiagramUniverseTensorIso I W B).inv =
      (weightedDiagramUniverseTensorIso I W A).inv ≫
        (weightedDiagramUniverse I).map (W ◁ (Functor.const I).map f) := by
  apply NatTrans.ext
  funext i
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨w, a⟩
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
