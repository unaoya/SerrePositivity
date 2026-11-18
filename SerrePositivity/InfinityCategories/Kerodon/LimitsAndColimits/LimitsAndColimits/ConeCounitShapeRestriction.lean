module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.FunctorHomCongrArrow
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ConeCounitHomUniversal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeCylinderShapeRestriction
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomotopyClasses

/-!
概要：元の錐の形状制限は、同じ指定余単位の前合成を保つ。
方針：元の円柱の自然性でホモトピーの全射を比較し、端点の表示は Arrow で相殺する。
使われ方：Kerodon §7.1（Tag 02H1）、HTT 6.2.2.6 の降下の合成。
規約：制限錐の頂点の等式も明示し、余単位を選び直さない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 制限した全錐の余単位は、元の余単位を同じ形状で前合成した射そのもの。 -/
lemma coneCounitHom_shapeRestriction {A K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (i : A ⟶ K) :
    kanFunctorHomCongr (V := i ≫ p) (SSet.comp_const i c.vertex) rfl
      ((hoFunctor.map ((pre i).app X)).toFunctor.map (coneCounitHom c)) =
    kanFunctorHomCongr (congrArg SSet.const (restrictJoinCone_vertex c i)) rfl
      (coneCounitHom (restrictJoinCone c i)) := by
  apply Arrow.mk_injective
  rw [kanFunctorHomCongr_arrow, kanFunctorHomCongr_arrow]
  change (hoFunctor.map ((pre i).app X)).toFunctor.mapArrow.obj
    (Arrow.mk (coneCounitHom c)) = _
  rw [coneCounitHom, kanFunctorHomCongr_arrow]
  change Arrow.mk ((hoFunctor.map ((pre i).app X)).toFunctor.map _) = _
  simp only [Arrow.mk_hom]
  rw [← functorHomotopyPrecomp_hom, coneCounitHom, kanFunctorHomCongr_arrow]
  apply functorHomotopy_hom_arrow_of_h_eq
  change (i ▷ (Δ[1] : SSet.{u})) ≫ coneCylinderMap K ≫ c.val =
    coneCylinderMap A ≫ joinMap (𝟙 (Δ[0] : SSet.{u})) i ≫ c.val
  rw [← Category.assoc, coneCylinderMap_naturality, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
