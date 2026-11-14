module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.AdjunctionCompositeCounit
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerHom
/-!
概要：合成 ∞ 随伴の余単位を、元の全関手の前後合成で回収する。
方針：双圏の結合子と単位子を明示し、同じ h Fun の射へ送る。
規約：指定余単位を保持する。使われ方：一般 kernel 随伴の余単位の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory MonoidalClosed Bicategory SSet
/-- 合成 ∞ 随伴の余単位を、元の全関手の前後合成で回収する。 -/
lemma QCatAdjunction.comp_counitHom
    {X Y Z : SSet.{u}} [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    {F : X ⟶ Y} {G : Y ⟶ X} {F' : Y ⟶ Z} {G' : Z ⟶ Y}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F' G') :
    (a.comp b).counitHom =
      (hoFunctor.map ((pre G').app Z)).toFunctor.map
        ((hoFunctor.map ((ihom Y).map F')).toFunctor.map a.counitHom) ≫ b.counitHom := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _) (Bicategory.Adjunction.compCounit a b) = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.bicategoryAdjunction_compCounit_explicit]
  simp only [Strict.associator_eqToIso, Strict.leftUnitor_eqToIso,
    eqToIso.hom, eqToIso.inv, eqToHom_refl,
    whiskerLeft_id, Category.id_comp]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G' ◁ (a.counit ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F')) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ b.counit = _
  have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerLeft (F := (G ≫ F) ≫ F') (G := F') G'
    (a.counit ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F')
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerRight (U := G ≫ F) (V := 𝟙 Y) a.counit F'
  exact congrArg (· ≫ b.counitHom) (hl.trans
    (congrArg ((hoFunctor.map ((pre G').app Z)).toFunctor.map) hr))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.QCatAdjunction (comp_counitHom)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
