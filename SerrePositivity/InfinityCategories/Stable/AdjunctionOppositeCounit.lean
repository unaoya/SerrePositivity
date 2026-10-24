module
public import SerrePositivity.InfinityCategories.Stable.CounitMappingAdjunction
/-!
概要：反対側の随伴の単位を、戻した随伴の同じ余単位へ同定する。
方針：全パラメータ Hom 対応の恒等射と、反対側の指定単位の回収を使う。
規約：元の h Fun の射を等式で保持する。使われ方：実 RHom 随伴の余単位の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed Bicategory SSet
open scoped Simplicial

/-- 反転 Hom 全単射は恒等射を保つ。 -/
lemma functorOppositeHomEquiv_id {A D : SSet.{u}} [Quasicategory D] (F : A ⟶ D) :
    SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv F F (𝟙 _) = 𝟙 _ := by
  let e := SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv F F
  have h := SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv_comp (𝟙 (HomotopyCategory.mk (functorVertex F)))
    (e.symm (𝟙 _))
  change e (𝟙 _ ≫ e.symm (𝟙 _)) = e (e.symm (𝟙 _)) ≫ e (𝟙 _) at h
  rw [Category.id_comp, Equiv.apply_symm_apply, Category.id_comp] at h
  exact h.symm

/-- 随伴の余単位の adjunct は、同じ右随伴の恒等射。 -/
lemma QCatAdjunction.homEquiv_counitHom {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : QCatAdjunction F G) : a.homEquiv G (𝟙 Y) a.counitHom = 𝟙 _ := by
  have h := (QCatFunctorHomCorrespondence.ofAdjunction a).toAdjunction_counitHom
  rw [QCatFunctorHomCorrespondence.ofAdjunction_toAdjunction] at h
  change a.counitHom = (a.homEquiv G (𝟙 Y)).symm _ at h
  rw [h, Equiv.apply_symm_apply]
  simp only [Strict.leftUnitor_eqToIso, eqToIso.inv, eqToHom_refl]
  exact (qcatHomFunctor Y X).map_id (qcatMap G)

/-- 同じ左随伴の恒等射の adjunct は、随伴の単位。 -/
lemma QCatAdjunction.homEquiv_id_unitHom {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : QCatAdjunction F G) : a.homEquiv (𝟙 X) F (𝟙 _) = a.unitHom := by
  have h := (QCatFunctorHomCorrespondence.ofAdjunction a).toAdjunction_unitHom
  rw [QCatFunctorHomCorrespondence.ofAdjunction_toAdjunction] at h
  change a.unitHom = a.homEquiv (𝟙 X) F _ at h
  rw [h]
  congr 1

/-- 反対側の随伴の単位は、元の随伴の余単位の反転と厳密に等しい。 -/
lemma qcatAdjunctionOfOpposite_counitHom {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : QCatAdjunction (opFunctor.map G) (opFunctor.map F)) :
    SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv (G ≫ F) (𝟙 Y)
      (qcatAdjunctionOfOpposite a).counitHom = a.unitHom := by
  have h := qcatAdjunctionOppositeHomEquiv_spec a G (𝟙 Y)
    (qcatAdjunctionOfOpposite a).counitHom
  rw [← qcatAdjunctionOfOpposite_homEquiv, QCatAdjunction.homEquiv_counitHom] at h
  change SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv G G (𝟙 _) = _ at h
  rw [functorOppositeHomEquiv_id] at h
  have he := congrArg (a.homEquiv (opFunctor.map (𝟙 Y)) (opFunctor.map G)) h
  rw [Equiv.apply_symm_apply] at he
  change a.homEquiv (𝟙 Y.op) (opFunctor.map G) (𝟙 _) = _ at he
  rw [a.homEquiv_id_unitHom] at he
  exact he.symm
end SerrePositivity.InfinityCategories
