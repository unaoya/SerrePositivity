module

public import SerrePositivity.KST.Spectra.PointedIhomActionNaturality
public import SerrePositivity.KST.Spectra.PointedIhomActionSuspension

/-!
概要：同じ実区間への内部 Hom の作用を、前合成・後合成と全区間で交換する。
方針：元の ihomAction の厳密自然性を同じ辺へ後合成する。
規約：Kan 性や区間の選び直しなし。使われ方：普遍的符号反転区間の反復 loop。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.PointedMapping.VerticalPath

/-- 標的への後合成と内部 Hom の作用は、同じ実辺全体で厳密に可換。 -/
lemma basedIhomMap_post_path (K : PointedSimplicialSet.{u})
    {A V Z : PointedSimplicialSet.{u}} {f g : A ⟶ V}
    (P : VerticalPath (PointedObject.toPoint V) f g) (v : V ⟶ Z) :
    ((P.basedPost v).basedIhomMap K).path =
      ((P.basedIhomMap K).basedPost (PointedObject.basedHomMap K v)).path := by
  rw [basedIhomMap_path]
  change (P.path ≫ (PointedObject.basedHomMap A v).right) ≫ _ =
    (P.basedIhomMap K).path ≫ _
  rw [basedIhomMap_path]
  have h := ihomAction_post K A v
  change PointedObject.basedHomMap A v ≫ ihomAction K A Z =
    ihomAction K A V ≫ PointedObject.basedHomMap (PointedObject.basedHom K A)
      (PointedObject.basedHomMap K v) at h
  simpa only [Under.comp_right, Category.assoc, PointedObject.ihom_obj_eq_basedHom] using
    congrArg (fun q => P.path ≫ q.right) h

/-- 源への前合成と内部 Hom の作用も、同じ実辺全体で厳密に可換。 -/
lemma basedIhomMap_pre_path_natural (K : PointedSimplicialSet.{u})
    {A B V : PointedSimplicialSet.{u}} {f g : A ⟶ V}
    (P : VerticalPath (PointedObject.toPoint V) f g) (j : B ⟶ A) :
    ((P.pre j).basedIhomMap K).path =
      ((P.basedIhomMap K).pre (PointedObject.basedHomMap K j)).path := by
  rw [basedIhomMap_path]
  change (P.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j V).right) ≫ _ = (P.basedIhomMap K).path ≫ _
  rw [basedIhomMap_path]
  have h := ihomAction_pre K j V
  change _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j V ≫ ihomAction K B V =
    ihomAction K A V ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.basedHomMap K j)
      (PointedObject.basedHom K V) at h
  simpa only [Under.comp_right, Category.assoc, PointedObject.ihom_obj_eq_basedHom] using
    congrArg (fun q => P.path ≫ q.right) h

end SerrePositivity.KST.Spectra.PointedMapping.VerticalPath
