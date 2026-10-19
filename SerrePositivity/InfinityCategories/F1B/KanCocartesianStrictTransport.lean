module

public import SerrePositivity.InfinityCategories.F1B.KanCocartesianSectionsPrecomposition
public import SerrePositivity.InfinityCategories.F1B.KanSectionRelativeEvaluation
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
概要：一般の cocartesian fibration の strict transport の図式と fiber への評価射を構成する。
方針：各 undercategory 上の cocartesian section を値とし、底の射には前合成を使う。
規約：全 section の弱い模型と区別し、fiber 比較の同値性は後続で証明する。
使われ方：Kerodon Construction 5.3.1.5 と一般の scaffold の係数。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open KanSection

/-- 概要：底の射から undercategory の nerve の反変な射を作る。
方針：Under.map の nerve を取る。
規約：f:c→d に対し nerve(d/C) から nerve(c/C) へ写す。
使われ方：Kerodon §5.3.1、strict transport の共変な射の前合成の始域。 -/
def kanCocartesianUnderMap {C : Type u} [Category.{u} C] {c d : C} (f : c ⟶ d) :
    nerve (Under d) ⟶ nerve (Under c) := nerveMap (Under.map f)

/-- 概要：undercategory の nerve の射は底 C の nerve への射影を保つ。
方針：under の射の標的を忘れる関手の定義を計算する。
規約：底の図式の整合性は厳密な等式。
使われ方：Kerodon §5.3.1、strict transport の相対関手空間の制限。 -/
lemma kanCocartesianUnderMap_projection {C : Type u} [Category.{u} C] {c d : C} (f : c ⟶ d) :
    kanCocartesianUnderMap f ≫ nerveMap (Under.forget c) = nerveMap (Under.forget d) := rfl

/-- 概要：undercategory の nerve の反変な射は恒等射を保つ。
方針：Under.map の恒等則を nerve に写す。
規約：自然同型ではなく射の等式を使う。
使われ方：Kerodon §5.3.1、strict transport の単位則。 -/
lemma kanCocartesianUnderMap_id {C : Type u} [Category.{u} C] (c : C) :
    kanCocartesianUnderMap (𝟙 c) = 𝟙 (nerve (Under c)) := by
  unfold kanCocartesianUnderMap
  rw [Under.mapId_eq]
  rfl

/-- 概要：undercategory の nerve の射は合成を逆順に保つ。
方針：Under.map の合成の等式を nerve に写す。
規約：f の後に g を合成する。
使われ方：Kerodon §5.3.1、strict transport の合成則。 -/
lemma kanCocartesianUnderMap_comp {C : Type u} [Category.{u} C] {c d e : C}
    (f : c ⟶ d) (g : d ⟶ e) :
    kanCocartesianUnderMap (f ≫ g) = kanCocartesianUnderMap g ≫ kanCocartesianUnderMap f := by
  unfold kanCocartesianUnderMap
  rw [Under.mapComp_eq]
  rfl

/-- 概要：strict transport の対象 c での値は c/C 上の cocartesian section の ∞ 圏。
方針：under の忘却関手の nerve 上の全部分相対関手空間を取る。
規約：p の充填性はこの定義には要求しない。
使われ方：一般の cocartesian fibration の strict な係数図式。 -/
def kanCocartesianStrictTransport {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) (c : C) : SSet.{u} :=
  kanCocartesianSections p (nerveMap (Under.forget c))

/-- 概要：底の射は undercategory の前合成で strict transport の射を誘導する。
方針：under の反変な射を cocartesian section の前合成へ渡す。
規約：得られる図式は底の圏 C に共変。
使われ方：Kerodon Construction 5.3.1.5 の射への作用。 -/
def kanCocartesianStrictTransportMap {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) {c d : C} (f : c ⟶ d) :
    kanCocartesianStrictTransport p c ⟶ kanCocartesianStrictTransport p d :=
  kanCocartesianSectionsPre p
    (Over.homMk (kanCocartesianUnderMap f) (kanCocartesianUnderMap_projection f) :
      Over.mk (nerveMap (Under.forget d)) ⟶ Over.mk (nerveMap (Under.forget c)))

/-- 概要：strict transport の射は恒等射を保つ。
方針：under の恒等射と section の前合成の恒等則を使う。
規約：厳密な等式。
使われ方：通常の関手への束縛。 -/
lemma kanCocartesianStrictTransportMap_id {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) (c : C) : kanCocartesianStrictTransportMap p (𝟙 c) = 𝟙 _ := by
  have hi : (Over.homMk (kanCocartesianUnderMap (𝟙 c))
      (kanCocartesianUnderMap_projection (𝟙 c)) :
      Over.mk (nerveMap (Under.forget c)) ⟶ Over.mk (nerveMap (Under.forget c))) = 𝟙 _ := by
    apply Over.OverMorphism.ext
    exact kanCocartesianUnderMap_id c
  unfold kanCocartesianStrictTransportMap
  rw [hi, kanCocartesianSectionsPre_id]
  rfl

/-- 概要：strict transport の射は合成を保つ。
方針：under の反変な合成則と section の前合成の合成則を使う。
規約：二つの前合成の反変性が打ち消し合う。
使われ方：通常の関手の合成則。 -/
lemma kanCocartesianStrictTransportMap_comp {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) {c d e : C} (f : c ⟶ d) (g : d ⟶ e) :
    kanCocartesianStrictTransportMap p (f ≫ g) =
      kanCocartesianStrictTransportMap p f ≫ kanCocartesianStrictTransportMap p g := by
  let i : Over.mk (nerveMap (Under.forget d)) ⟶ Over.mk (nerveMap (Under.forget c)) :=
    Over.homMk (kanCocartesianUnderMap f) (kanCocartesianUnderMap_projection f)
  let j : Over.mk (nerveMap (Under.forget e)) ⟶ Over.mk (nerveMap (Under.forget d)) :=
    Over.homMk (kanCocartesianUnderMap g) (kanCocartesianUnderMap_projection g)
  have hi : (Over.homMk (kanCocartesianUnderMap (f ≫ g))
      (kanCocartesianUnderMap_projection (f ≫ g)) :
      Over.mk (nerveMap (Under.forget e)) ⟶ Over.mk (nerveMap (Under.forget c))) = j ≫ i := by
    apply Over.OverMorphism.ext
    exact kanCocartesianUnderMap_comp f g
  change kanCocartesianSectionsPre p _ = kanCocartesianSectionsPre p i ≫
    kanCocartesianSectionsPre p j
  rw [hi, kanCocartesianSectionsPre_comp]

/-- 概要：cocartesian section の strict transport の単体集合値図式。
方針：構成した対象と射を恒等・合成則で束縛する。
規約：各値の quasicategory 性は別の instance で与える。
使われ方：一般の universal scaffold の simplicial replacement の係数。 -/
def kanCocartesianStrictTransportDiagram {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) : C ⥤ SSet.{u} where
  obj c := kanCocartesianStrictTransport p c
  map f := kanCocartesianStrictTransportMap p f
  map_id c := kanCocartesianStrictTransportMap_id p c
  map_comp f g := kanCocartesianStrictTransportMap_comp p f g

/-- 概要：inner fibration の strict transport の各値は quasicategory。
方針：cocartesian section の全部分空間の充填性を使う。
規約：Kan 複体であるとは仮定しない。
使われ方：一般の QCat 値の strict transport の値。 -/
instance kanCocartesianStrictTransport_quasicategory
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [InnerFibration p] (c : C) :
    Quasicategory (kanCocartesianStrictTransport p c) :=
  kanCocartesianSections_quasicategory p _

/-- 概要：strict transport の係数図式は quasicategory 値。
方針：各値の cocartesian section の quasicategory 性を図式の型へ渡す。
規約：必要な仮定は inner fibration 性だけ。
使われ方：一般の scaffold の係数条件。 -/
instance kanCocartesianStrictTransportDiagram_quasicategory
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [InnerFibration p] (c : C) :
    Quasicategory ((kanCocartesianStrictTransportDiagram p).obj c) :=
  kanCocartesianStrictTransport_quasicategory p c

/-- 概要：cocartesian な section を undercategory の恒等射で評価する。
方針：元の全 section の評価へ全部分複体の包含を合成する。
規約：この段階では比較射を構成するだけで、同値性は主張しない。
使われ方：strict transport と元の fiber の比較。 -/
def kanCocartesianStrictTransportEvaluate {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) (c : C) :
    kanCocartesianStrictTransport p c ⟶ vertexFiber p (nerveVertex c) :=
  kanCocartesianSectionsι p (nerveMap (Under.forget c)) ≫
    relativeFunctorEvaluate p (nerveMap (Under.forget c))
      ((nerveEquiv (C := Under c)).symm (Under.mk (𝟙 c)))

end SerrePositivity.InfinityCategories
