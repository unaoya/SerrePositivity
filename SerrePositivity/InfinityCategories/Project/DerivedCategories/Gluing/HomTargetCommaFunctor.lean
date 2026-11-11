module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetCommaComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetCommaUnit
/-!
概要：元の共通終域を持つ Hom gluing から実 comma への dg 比較関手を構成する。
方針：全 Hom の鎖写像と検証済みの単位・合成則を束ねる。
規約：元の両脚と第三 cochain を保持し、加群値の正本比較とは区別する。
使われ方：Milnor の元 Perf 二脚を持つ比較の接続に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
def dgGluingHomTargetToComma :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R D E q) where
  obj := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q
  map := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap R C D E p q
  map_id X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap_identity R C D E p q X
  map_comp X Y Z := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap_composition R C D E p q X Y Z
lemma dgGluingHomTargetToComma_source :
    (dgGluingHomTargetToComma R C D E p q).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R D E q) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D (dgHomGluingBimodule R C D E p q) := by
  apply EnrichedFunctor.ext (Complex R)
  case h_obj => intro X; rfl
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap R C D E p q X Y ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R D E q _ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight_map]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap_source R C D E p q X Y
lemma dgGluingHomTargetToComma_replacement :
    (dgGluingHomTargetToComma R C D E p q).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R D E q) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D (dgHomGluingBimodule R C D E p q)).comp p := by
  apply EnrichedFunctor.ext (Complex R)
  case h_obj => intro X; rfl
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap R C D E p q X Y ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R D E q _ _ = _
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap_replacement R C D E p q X Y
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
