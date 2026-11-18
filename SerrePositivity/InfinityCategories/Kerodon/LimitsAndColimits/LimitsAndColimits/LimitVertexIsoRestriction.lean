module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitVertexIsoComposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceProjectionLaws

/-!
概要：同じ標準極限比較を制限した頂点射は、頂点の等式による移送に両立する。
方針：錐の標準比較の制限の法則を、同じ頂点射影の等式の自然性で写す。
規約：HTT §1.2.13、Kerodon §7.1（Tag 02H1）の既存の制限と比較の法則。
使われ方：S8 の同値な添字での固定値比較の合成を照合する。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
variable {K L X : SSet.{u}} [Quasicategory X] {O : L ⟶ X}

/-- 元の標準極限比較の制限は、同じ頂点等式を通して元の頂点比較になる。 -/
lemma limitVertexIso_restrict_hom (f : K ⟶ L) (d e : JoinCone O)
    (hd : IsLimitCone d) (he : IsLimitCone e)
    (hdf : IsLimitCone (restrictJoinCone d f))
    (hef : IsLimitCone (restrictJoinCone e f)) :
    eqToHom (congrArg HomotopyCategory.mk (restrictJoinCone_vertex d f)) ≫
        (limitVertexIso d e hd he).hom =
      (limitVertexIso (restrictJoinCone d f) (restrictJoinCone e f) hdf hef).hom ≫
        eqToHom (congrArg HomotopyCategory.mk (restrictJoinCone_vertex e f)) := by
  have hp : (hoFunctor.map (sliceOverRestrict O f)).toFunctor ⋙
      (hoFunctor.map (sliceOverProjection (f ≫ O))).toFunctor =
        (hoFunctor.map (sliceOverProjection O)).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp,
      sliceOverRestrict_projection]
  have h := (eqToHom hp).naturality (limitConeIso d e hd he).hom
  simp only [eqToHom_app] at h
  change (hoFunctor.map (sliceOverProjection (f ≫ O))).toFunctor.map
      ((hoFunctor.map (sliceOverRestrict O f)).toFunctor.map (limitConeIso d e hd he).hom) ≫
        eqToHom _ = eqToHom _ ≫
          (hoFunctor.map (sliceOverProjection O)).toFunctor.map
            (limitConeIso d e hd he).hom at h
  rw [limitConeIso_restrict_hom f d e hd he hdf hef] at h
  exact h.symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
