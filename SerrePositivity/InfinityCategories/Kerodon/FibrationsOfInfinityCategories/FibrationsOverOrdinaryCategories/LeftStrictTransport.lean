module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveUnderMap

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
概要：通常の圏上の left fibration の Kan 値 strict transport 表現。
方針：各 undercategory の nerve 上の相対関手単体集合を取り、射には前合成を使う。
規約：left fibration の全ての辺は cocartesian なので、追加の頂点制限は不要。
使われ方：Kerodon Construction 5.3.1.5（Tag 035J）、空間値 strict transport の対象と射。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：底の対象 c における left fibration の strict transport の単体集合。
方針：c/C の nerve から全空間への、底を固定した関手単体集合を取る。
規約：p の left fibration 性は対象の定義には含めない。
使われ方：Kerodon Construction 5.3.1.5（Tag 035J）、strict transport の空間値。 -/
def leftStrictTransport {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) (c : C) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p (nerveMap (Under.forget c))

/-- 概要：底の射に沿う strict transport の射。
方針：undercategory の反変な nerve の射で相対関手を前合成する。
規約：射は単体集合の実際の射であり、ホモトピー類への商ではない。
使われ方：Kerodon Construction 5.3.1.5（Tag 035J）、strict transport の関手の射への作用。 -/
def leftStrictTransportMap {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) {c d : C} (f : c ⟶ d) :
    leftStrictTransport p c ⟶ leftStrictTransport p d :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p (nerveMap (Under.forget c)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f)

/-- 概要：strict transport は底の恒等射を恒等射へ写す。
方針：相対関手空間の包含後に nerveUnderMap と前合成の恒等則を計算する。
規約：恒等則は射の等式として成立する。
使われ方：Kerodon §5.3.1（Tag 035D）、strict transport 表現の関手性。 -/
lemma leftStrictTransportMap_id {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) (c : C) : leftStrictTransportMap p (𝟙 c) = 𝟙 _ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom (nerve (Under c))).map p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (nerveMap (Under.forget c)))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _ ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap (𝟙 c))).app E = 𝟙 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_id, pre_id, NatTrans.id_app, Category.comp_id, Category.id_comp]

/-- 概要：strict transport は底の射の合成を保つ。
方針：相対関手空間の包含後に undercategory の反変性と前合成の合成則を使う。
規約：二つの反変性の合成により共変な表現になる。
使われ方：Kerodon §5.3.1（Tag 035D）、strict transport 表現の関手の合成則。 -/
lemma leftStrictTransportMap_comp {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) {c d e : C} (f : c ⟶ d) (g : d ⟶ e) :
    leftStrictTransportMap p (f ≫ g) = leftStrictTransportMap p f ≫ leftStrictTransportMap p g := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom (nerve (Under e))).map p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (nerveMap (Under.forget e)))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _ ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap (f ≫ g))).app E =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _ ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f)).app E) ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap g)).app E
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_comp, pre_map, NatTrans.comp_app, Category.assoc]

/-- 概要：left fibration の strict transport の各値は Kan 複体。
方針：left fibration 上の相対関手単体集合の Kan 性を適用する。
規約：全空間 E の quasicategory 性は別に仮定しない。
使われ方：Kerodon Construction 5.3.1.5（Tag 035J）、Kan 値表現への束縛。 -/
instance leftStrictTransport_kanComplex {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (c : C) : KanComplex (leftStrictTransport p c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace_kanComplex p _

/-- 概要：left fibration から通常の圏上の Kan 値 strict transport 関手を構成する。
方針：相対関手空間と undercategory による前合成を KanObject の関手に束縛する。
規約：各 fiber との比較と元の fibration の復元は別の証明課題。
使われ方：Kerodon Construction 5.3.1.5（Tag 035J）、空間値 straightening の strict 表現。 -/
def leftStrictTransportFunctor {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} where
  obj c := ⟨leftStrictTransport p c, inferInstance⟩
  map f := leftStrictTransportMap p f
  map_id c := leftStrictTransportMap_id p c
  map_comp f g := leftStrictTransportMap_comp p f g

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
