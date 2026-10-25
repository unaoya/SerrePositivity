module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCommaComposition
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCommaUnit
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
def dgGluingHomTargetToComma :
    DGFunctor R (DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
      (DGFunctorCommaObject R D E q) where
  obj := dgGluingHomTargetCommaObject R C D E p q
  map := dgGluingHomTargetCommaHomMap R C D E p q
  map_id X := dgGluingHomTargetCommaHomMap_identity R C D E p q X
  map_comp X Y Z := dgGluingHomTargetCommaHomMap_composition R C D E p q X Y Z
lemma dgGluingHomTargetToComma_source :
    (dgGluingHomTargetToComma R C D E p q).comp (dgFunctorCommaSource R D E q) =
      dgGluingRight R C D (dgHomGluingBimodule R C D E p q) := by
  apply EnrichedFunctor.ext (Complex R)
  case h_obj => intro X; rfl
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  change dgGluingHomTargetCommaHomMap R C D E p q X Y ≫
    dgFunctorCommaSourceHomMap R D E q _ _ = _
  rw [dgGluingRight_map]
  exact dgGluingHomTargetCommaHomMap_source R C D E p q X Y
lemma dgGluingHomTargetToComma_replacement :
    (dgGluingHomTargetToComma R C D E p q).comp (dgFunctorCommaReplacement R D E q) =
      (dgGluingLeft R C D (dgHomGluingBimodule R C D E p q)).comp p := by
  apply EnrichedFunctor.ext (Complex R)
  case h_obj => intro X; rfl
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  change dgGluingHomTargetCommaHomMap R C D E p q X Y ≫
    dgFunctorCommaReplacementHomMap R D E q _ _ = _
  exact dgGluingHomTargetCommaHomMap_replacement R C D E p q X Y
end SerrePositivity.InfinityCategories
