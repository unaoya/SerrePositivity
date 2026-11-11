module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveIdempotence
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.AdjunctionUnitInvertible

/-!
概要：反射単位の包含に沿った制限と反射による像の可逆性。
方針：可逆な余単位を三角恒等式から相殺し、左右 whisker を h Fun に移す。
規約：単位全体の可逆性を仮定・結論しない。
使われ方：B2 の反射像の局所性と、局所化が反転する辺の特定。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Bicategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
local instance unitInvertibleHomCategory (A B : SSet.QCat.{u}) : Category.{u} (A ⟶ B) :=
  SSet.QCat.bicategory.homCategory A B

/-- 概要：可逆な余単位を持つ随伴の単位の右随伴に沿う制限は可逆。
方針：右三角恒等式の一般補題と左 whisker の h Fun 表示を使う。
規約：h Fun 全体の可逆性。使われ方：反射部分圏上の単位。 -/
lemma QCatAdjunction.unit_precompRight_isIso
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) [IsIso a.counit] :
    IsIso ((hoFunctor.map ((pre G).app X)).toFunctor.map a.unitHom) := by
  haveI : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G ◁ a.unit) := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategory_whiskerLeft_unit_isIso_of_counit a
  have h : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G ◁ a.unit)) := by
    change IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor Y X).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G ◁ a.unit))
    infer_instance
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerLeft G a.unit) ▸ h

/-- 概要：可逆な余単位を持つ随伴の左随伴による単位の像は可逆。
方針：左三角恒等式の一般補題と右 whisker の h Fun 表示を使う。
規約：h Fun 全体の可逆性。使われ方：反射がその単位を反転する性質。 -/
lemma QCatAdjunction.unit_postcompLeft_isIso
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) [IsIso a.counit] :
    IsIso ((hoFunctor.map ((ihom X).map F)).toFunctor.map a.unitHom) := by
  haveI : IsIso (a.unit ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F) := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategory_whiskerRight_unit_isIso_of_counit a
  have h : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (a.unit ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F)) := by
    change IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor X Y).map (a.unit ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F))
    infer_instance
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerRight a.unit F) ▸ h

namespace ReflectiveSubcategory
variable {X : SSet.{u}} [Quasicategory X] {P : X _⦋0⦌ → Prop}
variable (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory X P)

/-- 概要：反射の単位は包含に沿って制限すると自然同型。
方針：可逆な余単位を持つ随伴の単位の制限の一般補題を使う。
規約：同型の順射は元の単位の制限。使われ方：部分圏の像の局所性。 -/
def unitOnInclusionIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι ≫ r.localization) := by
  haveI := r.adjunction.unit_precompRight_isIso
  let e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι ≫ 𝟙 X)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι ≫ r.localization) :=
    asIso ((hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι).app X)).toFunctor.map
      r.adjunction.unitHom)
  simpa only [Category.comp_id] using e

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveSubcategory (unitOnInclusionIso)


/-- 概要：反射で写した単位は自然同型。
方針：可逆な余単位を持つ随伴の単位の像の一般補題を使う。
規約：同型の順射は元の単位の反射。使われ方：反射が反転する単位。 -/
def reflectedUnitIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso r.reflector (r.localization ≫ r.reflector) := by
  haveI := r.adjunction.unit_postcompLeft_isIso
  let e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((𝟙 X) ≫ r.reflector) (r.localization ≫ r.reflector) :=
    asIso ((hoFunctor.map ((ihom X).map r.reflector)).toFunctor.map r.adjunction.unitHom)
  simpa only [Category.id_comp] using e

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveSubcategory (reflectedUnitIso)


/-- 概要：反射の単位は反射像に沿って制限すると自然同型。
方針：包含上の単位同型を反射関手に沿って前合成する。
規約：h Fun の L→L² の同型。使われ方：冪等性と局所対象。 -/
def unitOnLocalizationIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso r.localization (r.localization ≫ r.localization) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.localization, Category.assoc] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp r.unitOnInclusionIso r.reflector

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveSubcategory (unitOnLocalizationIso)


end ReflectiveSubcategory
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
