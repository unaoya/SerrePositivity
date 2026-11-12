module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveUnderMap

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianSectionsPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorEvaluation
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：一般の cocartesian fibration の strict transport の図式と fiber への評価射を構成する。
方針：各 undercategory 上の cocartesian section を値とし、底の射には前合成を使う。
規約：全 section の弱い模型と区別し、fiber 比較の同値性は後続で証明する。
使われ方：Kerodon Construction 5.3.1.5（Tag 035J） と一般の scaffold の係数。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open _root_.SerrePositivity.InfinityCategories

/-- 概要：strict transport の対象 c での値は c/C 上の cocartesian section の ∞ 圏。
方針：under の忘却関手の nerve 上の全部分相対関手空間を取る。
規約：p の充填性はこの定義には要求しない。
使われ方：一般の cocartesian fibration の strict な係数図式。 -/
@[kerodon 035J]
def cocartesianStrictTransport {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) (c : C) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p (nerveMap (Under.forget c))

/-- 概要：底の射は undercategory の前合成で strict transport の射を誘導する。
方針：under の反変な射を cocartesian section の前合成へ渡す。
規約：得られる図式は底の圏 C に共変。
使われ方：Kerodon Construction 5.3.1.5（Tag 035J） の射への作用。 -/
def cocartesianStrictTransportMap {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) {c d : C} (f : c ⟶ d) :
    cocartesianStrictTransport p c ⟶ cocartesianStrictTransport p d :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre p
    (Over.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_projection f) :
      Over.mk (nerveMap (Under.forget d)) ⟶ Over.mk (nerveMap (Under.forget c)))

/-- 概要：strict transport の射は恒等射を保つ。
方針：under の恒等射と section の前合成の恒等則を使う。
規約：厳密な等式。
使われ方：通常の関手への束縛。 -/
lemma cocartesianStrictTransportMap_id {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) (c : C) : cocartesianStrictTransportMap p (𝟙 c) = 𝟙 _ := by
  have hi : (Over.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap (𝟙 c))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_projection (𝟙 c)) :
      Over.mk (nerveMap (Under.forget c)) ⟶ Over.mk (nerveMap (Under.forget c))) = 𝟙 _ := by
    apply Over.OverMorphism.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_id c
  unfold cocartesianStrictTransportMap
  rw [hi, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre_id]
  rfl

/-- 概要：strict transport の射は合成を保つ。
方針：under の反変な合成則と section の前合成の合成則を使う。
規約：二つの前合成の反変性が打ち消し合う。
使われ方：通常の関手の合成則。 -/
lemma cocartesianStrictTransportMap_comp {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) {c d e : C} (f : c ⟶ d) (g : d ⟶ e) :
    cocartesianStrictTransportMap p (f ≫ g) =
      cocartesianStrictTransportMap p f ≫ cocartesianStrictTransportMap p g := by
  let i : Over.mk (nerveMap (Under.forget d)) ⟶ Over.mk (nerveMap (Under.forget c)) :=
    Over.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_projection f)
  let j : Over.mk (nerveMap (Under.forget e)) ⟶ Over.mk (nerveMap (Under.forget d)) :=
    Over.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_projection g)
  have hi : (Over.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap (f ≫ g))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_projection (f ≫ g)) :
      Over.mk (nerveMap (Under.forget e)) ⟶ Over.mk (nerveMap (Under.forget c))) = j ≫ i := by
    apply Over.OverMorphism.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_comp f g
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre p _ = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre p i ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre p j
  rw [hi, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre_comp]

/-- 概要：cocartesian section の strict transport の単体集合値図式。
方針：構成した対象と射を恒等・合成則で束縛する。
規約：各値の quasicategory 性は別の instance で与える。
使われ方：一般の universal scaffold の simplicial replacement の係数。 -/
@[kerodon 035J]
def cocartesianStrictTransportDiagram {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) : C ⥤ SSet.{u} where
  obj c := cocartesianStrictTransport p c
  map f := cocartesianStrictTransportMap p f
  map_id c := cocartesianStrictTransportMap_id p c
  map_comp f g := cocartesianStrictTransportMap_comp p f g

/-- 概要：inner fibration の strict transport の各値は quasicategory。
方針：cocartesian section の全部分空間の充填性を使う。
規約：Kan 複体であるとは仮定しない。
使われ方：一般の QCat 値の strict transport の値。 -/
instance cocartesianStrictTransport_quasicategory
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [InnerFibration p] (c : C) :
    Quasicategory (cocartesianStrictTransport p c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections_quasicategory p _

/-- 概要：strict transport の係数図式は quasicategory 値。
方針：各値の cocartesian section の quasicategory 性を図式の型へ渡す。
規約：必要な仮定は inner fibration 性だけ。
使われ方：一般の scaffold の係数条件。 -/
instance cocartesianStrictTransportDiagram_quasicategory
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [InnerFibration p] (c : C) :
    Quasicategory ((cocartesianStrictTransportDiagram p).obj c) :=
  cocartesianStrictTransport_quasicategory p c

/-- 概要：cocartesian な section を undercategory の恒等射で評価する。
方針：元の全 section の評価へ全部分複体の包含を合成する。
規約：この段階では比較射を構成するだけで、同値性は主張しない。
使われ方：strict transport と元の fiber の比較。 -/
def cocartesianStrictTransportEvaluate {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) (c : C) :
    cocartesianStrictTransport p c ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι p (nerveMap (Under.forget c)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate p (nerveMap (Under.forget c))
      ((nerveEquiv (C := Under c)).symm (Under.mk (𝟙 c)))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
