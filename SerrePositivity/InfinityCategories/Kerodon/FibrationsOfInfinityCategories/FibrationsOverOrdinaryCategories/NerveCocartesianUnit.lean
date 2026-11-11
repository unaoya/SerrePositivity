module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveCocartesianScaffold
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NerveTransportUnit
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianSectionFamilies
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：係数図式から weighted nerve の cocartesian strict transport への自然な比較。
方針：taut scaffold の under 評価を cocartesian section の族へ curry する。
規約：係数値は quasicategory。全次数の同じ比較を元の section 空間へ含めて照合する。
使われ方：Cat∞ 値 straightening と unstraightening の strict 図式での比較。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- under 評価で係数の頂点を固定した各辺は最後の係数が可逆となる。 -/
lemma tautScaffold_underEvaluation_isCocartesian {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)] (c : C)
    (x : (F.obj c) _⦋0⦌) (e : (nerve (Under c)) _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementUnderEvaluation F c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold F).app _
        (e, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.isCocartesianEdge_weightedNerve_of_coefficient
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv
    (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion 1 1 _) ≫
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) ≫ F.map (e.obj 0).hom) ≫
      F.map ((e ⋙ Under.forget c).map (homOfLE (Fin.zero_le (Fin.last 1)))))))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_id, CategoryTheory.Functor.map_id, Category.id_comp]
  have hx : SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) = SSet.const x := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv.apply_symm_apply]
    rfl
  rw [hx, SSet.const_comp, SSet.const_comp]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_map_const _ 0

/-- 係数の値を、同じ taut scaffold が定める cocartesian section の族へ写す。 -/
def weightedNerveCocartesianUnitComponent {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)] (c : C) :
    F.obj c ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) c :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsCurry
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementUnderEvaluation F c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold F) (by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_projection,
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementUnderEvaluation_projection])
    (tautScaffold_underEvaluation_isCocartesian F c)

/-- cocartesian section の包含後には、既存の標準単位の全次数の射と一致する。 -/
lemma weightedNerveCocartesianUnitComponent_ι {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)] (c : C) :
    weightedNerveCocartesianUnitComponent F c ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) (nerveMap (Under.forget c)) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit F).app c := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro m α
  apply ConcreteCategory.hom_ext
  intro τ
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit_app F c n m x α τ).symm

/-- 元の係数図式から cocartesian strict transport への図式全体の自然変換。 -/
@[kerodon 037B]
def weightedNerveCocartesianTransportUnit {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)] :
    F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) where
  app := weightedNerveCocartesianUnitComponent F
  naturality c d f := by
    apply (cancel_mono
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) (nerveMap (Under.forget d)))).1
    rw [Category.assoc, weightedNerveCocartesianUnitComponent_ι]
    let i : Over.mk (nerveMap (Under.forget d)) ⟶
        Over.mk (nerveMap (Under.forget c)) :=
      Over.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_projection f)
    have hpre := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre_ι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) i
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) i ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) (nerveMap (Under.forget d)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) (nerveMap (Under.forget c)) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F)).map f at hpre
    calc
      _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit F).app c ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F)).map f :=
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit F).naturality f
      _ = (weightedNerveCocartesianUnitComponent F c ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) (nerveMap (Under.forget c))) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F)).map f := by
        rw [weightedNerveCocartesianUnitComponent_ι]
      _ = weightedNerveCocartesianUnitComponent F c ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) i ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) (nerveMap (Under.forget d))) := by
        rw [Category.assoc, hpre]
      _ = _ := (Category.assoc _ _ _).symm

/-- cocartesian 比較を恒等射で評価すると元の標準 fiber 同型となる。 -/
lemma weightedNerveCocartesianTransportUnit_evaluate {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)] (c : C) :
    (weightedNerveCocartesianTransportUnit F).app c ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportEvaluate (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) c =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveFiberMap F c := by
  change weightedNerveCocartesianUnitComponent F c ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) (nerveMap (Under.forget c)) ≫ _) = _
  rw [← Category.assoc, weightedNerveCocartesianUnitComponent_ι]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit_evaluate F c

/-- 同じ図式全体の cocartesian 比較は各対象で ∞ 圏の同値。 -/
@[kerodon 037B]
lemma weightedNerveCocartesianTransportUnit_isQCatEquivalence {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)] (c : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((weightedNerveCocartesianTransportUnit F).app c) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportEvaluate_isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) c).cancel_right
  rw [weightedNerveCocartesianTransportUnit_evaluate]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveFiberIso F c)).isQCatEquivalence

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
