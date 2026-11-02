module

public import SerrePositivity.InfinityCategories.F2.Idempotent.IdemLeftCofinality
public import SerrePositivity.InfinityCategories.Core.ColimitReindex

/-!
概要：元の分裂対象での左 Kan 局所添字は、元の Idem と射影により同型。
方針：元の comma との native 比較と、元の左 comma の射影同型を合成する。
規約：局所図式は元の Idem 図式の同じ射影への前合成そのもの。
使われ方：元の冪等図式の余極限から、分裂対象での左局所余極限を作る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の分裂対象での元の左局所添字と、元の全 Idem の指定同型。 -/
def idemImageKanShapeIso :
    leftKanShape idemInclusion (nerveVertex walkingImage.{u}) ≅ IdemShape :=
  (walkingLeftCommaSliceIso walkingImage).symm ≪≫ nerveFunctor.mapIso walkingImageLeftCommaIso

/-- 指定した同型の順方向は、元の全 Idem への元の射影そのもの。 -/
lemma idemImageKanShapeIso_projection : idemImageKanShapeIso.{u}.hom =
    leftKanProjection idemInclusion (nerveVertex walkingImage) := by
  apply (cancel_epi (walkingLeftCommaSliceIso walkingImage).hom).mp
  change (walkingLeftCommaSliceIso walkingImage).hom ≫
    ((walkingLeftCommaSliceIso walkingImage).inv ≫
      (nerveFunctor.mapIso walkingImageLeftCommaIso).hom) = _
  exact ((walkingLeftCommaSliceIso walkingImage).hom_inv_id_assoc _).trans
    (walkingLeftCommaSliceIso_projection walkingImage).symm

/-- 元の分裂対象での元の左局所射影そのものは同型。 -/
instance idemImageKanProjection_isIso :
    IsIso (leftKanProjection idemInclusion (nerveVertex walkingImage.{u})) := by
  rw [← idemImageKanShapeIso_projection]
  infer_instance

/-- 元の Idem 図式の余極限は、同じ分裂対象での元の左局所余極限を与える。 -/
lemma idemImageKanDiagram_hasColimit {X : SSet.{u}} [Quasicategory X]
    (d : CoherentIdempotent X) (hd : HasColimit d) :
    HasColimit (leftKanDiagram idemInclusion d (nerveVertex walkingImage)) := by
  obtain ⟨c, hc⟩ := hd
  let p := leftKanProjection idemInclusion (nerveVertex walkingImage.{u})
  exact ⟨c.restrict p, (isColimitCone_iff_restrict_of_isIso c p).mp hc⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
