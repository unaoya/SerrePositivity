module
public import SerrePositivity.HomologicalAlgebra.LinearWeightEndTotalization

/-!
概要：線形重みの end の積全複体を、係数図式と重みの鎖複体の両方に関手化する。
方針：各次数の線形 end の自然変換を余鎖複体へ移し、同じ積全複体関手で後合成する。
規約：係数に共変、重みに反変。比較射を選び直さず自然変換として保持する。
使われ方：HA 1.2.4、G10 の指定比較と元の図式の全射との両立。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

local instance (X : Jᵒᵖ ⥤ Complex A) : ((linearWeightEndFamily A).obj X).Additive :=
  linearWeightEnd_additive A X

/-- 元の係数図式の射から、重みの全鎖複体上の同じ余鎖 end の自然変換を作る。 -/
def linearWeightEndCochainMap {X Y : Jᵒᵖ ⥤ Complex A} (f : X ⟶ Y) :
    linearWeightEndCochainFunctor A X ⟶ linearWeightEndCochainFunctor A Y :=
  Functor.whiskerLeft (HomologicalComplex.opFunctor (Jᵒᵖ ⥤ ModuleCat.{u} A) (.down ℕ))
    (((linearWeightEndFamily A).map f).mapHomologicalComplex (.up ℕ))

/-- 同じ係数の自然変換を、線形 end の積全複体へ移す。 -/
def linearWeightEndTotalMap {X Y : Jᵒᵖ ⥤ Complex A} (f : X ⟶ Y) :
    linearWeightEndTotalFunctor A X ⟶ linearWeightEndTotalFunctor A Y :=
  Functor.whiskerRight (linearWeightEndCochainMap A f)
    (cochainProductTotalizationFunctor (ModuleCat.{u} A))

/-- 係数図式の全射と重みの全鎖写像を保持する、線形 end の積全複体の全関手族。 -/
def linearWeightEndTotalFamily :
    (Jᵒᵖ ⥤ Complex A) ⥤ (ChainComplex (Jᵒᵖ ⥤ ModuleCat.{u} A) ℕ)ᵒᵖ ⥤ Complex A where
  obj X := linearWeightEndTotalFunctor A X
  map f := linearWeightEndTotalMap A f
  map_id X := by
    simp only [linearWeightEndTotalMap, linearWeightEndCochainMap,
      CategoryTheory.Functor.map_id, NatTrans.mapHomologicalComplex_id]
    apply NatTrans.ext
    funext K
    change (cochainProductTotalizationFunctor (ModuleCat.{u} A)).map (𝟙 _) = 𝟙 _
    exact (cochainProductTotalizationFunctor (ModuleCat.{u} A)).map_id _
  map_comp f g := by
    simp only [linearWeightEndTotalMap, linearWeightEndCochainMap,
      CategoryTheory.Functor.map_comp, NatTrans.mapHomologicalComplex_comp,
      Functor.whiskerLeft_comp, Functor.whiskerRight_comp]

/-- 同じ重みの鎖写像による比較は、元の係数図式の全射に自然。 -/
theorem linearWeightEndTotalMap_naturality {X Y : Jᵒᵖ ⥤ Complex A} (f : X ⟶ Y)
    {K L : ChainComplex (Jᵒᵖ ⥤ ModuleCat.{u} A) ℕ} (g : K ⟶ L) :
    (linearWeightEndTotalFunctor A X).map g.op ≫ (linearWeightEndTotalMap A f).app (op K) =
      (linearWeightEndTotalMap A f).app (op L) ≫ (linearWeightEndTotalFunctor A Y).map g.op :=
  (linearWeightEndTotalMap A f).naturality g.op

end SerrePositivity.HomologicalAlgebra
