module
public import SerrePositivity.DifferentialGraded.Endomorphism.LargeHomBimodule
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule
public import SerrePositivity.DifferentialGraded.Tensor.RightUnit

/-! # 実際のdg加群EによるHomとtensorの比較関手

全右加群の対象型をsmallとは仮定しない。随伴性と導来化は別の証明義務。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- 全加群dg圏上のHom(E,−)関手。Hom(E,M)は元の全Hom end。 -/
def endomorphismModuleHom : DGFunctor A (RightModule A D)
    (RightModule A (EndomorphismObject E)) :=
  (largeEndomorphismHomBimodule A (RightModule A D) E).toFunctor

/-- Eに残る右D・左End(E)作用。閉零自己射だけに制限しない。 -/
def endomorphismModuleAction : Bimodule A D (EndomorphismObject E) :=
  endomorphismInclusion A E

/-- 右End(E)加群をEとtensorする、全次数自然な再構成側のdg関手。 -/
def endomorphismModuleTensor : DGFunctor A (RightModule A (EndomorphismObject E))
    (RightModule A D) :=
  (BimoduleTensor.compose A D (EndomorphismObject E) (RightModule A (EndomorphismObject E))
    (endomorphismModuleAction A D E)
    (DGFunctor.id (RightModule A (EndomorphismObject E)))).toFunctor

/-- Hom側の値は全Hom endである。 -/
lemma endomorphismModuleHom_value (M : RightModule A D) (b : EndomorphismObject E) :
    ((endomorphismModuleHom A D E).obj M).obj (op b) = moduleHom A D E M := rfl

/-- tensor側の値は既存のbalanced tensorを使う。 -/
lemma endomorphismModuleTensor_value (M : RightModule A (EndomorphismObject E)) (d : D) :
    ((endomorphismModuleTensor A D E).obj M).obj (op d) =
      BalancedTensor.obj A (EndomorphismObject E) M ((endomorphismModuleAction A D E).leftAt d) :=
  rfl

/-- 指定対象のHom像は正則End(E)加群。全加群型のsmall性は不要。 -/
lemma endomorphismModuleHom_self :
    (endomorphismModuleHom A D E).obj E =
      representable A (EndomorphismObject.point (E := E)) :=
  endomorphismHomRight_self A (RightModule A D) E

/-- 正則End(E)加群のtensor像は元のEに戻る。既存Yoneda tensor単位との比較。 -/
def endomorphismModuleTensor_regularIso :
    ForgetEnrichment.of (Complex A)
        ((endomorphismModuleTensor A D E).obj
          (representable A (EndomorphismObject.point (E := E)))) ≅
      ForgetEnrichment.of (Complex A) E :=
  BimoduleTensor.rightUnitIso A D (EndomorphismObject E)
    (endomorphismModuleAction A D E) .point

/-- U13の指定perfect対象から得るtensor側。Eは実際のdg加群として保持する。 -/
abbrev perfectEndomorphismModuleTensor (S : Set D) (E : PerfectDGModuleOver A D S) :=
  endomorphismModuleTensor A D E.val

end SerrePositivity.DifferentialGraded
