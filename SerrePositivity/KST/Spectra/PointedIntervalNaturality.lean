module

public import SerrePositivity.KST.Spectra.PointedBasedPathDifference
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointParameterStructure

/-!
概要：同じ実区間の前合成・後合成・列の構造像の交換則。
方針：内部 Hom の自然性と懸垂の豊穣後合成の自然性を、元の辺全体へ作用させる。
規約：区間の選択は不要。使われ方：全 Hom 区間の源単位への評価の構造条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.PointedMapping.VerticalPath

/-- 同じ元の区間に前合成・後合成する順序は、区間全体で厳密に可換。 -/
lemma pre_basedPost_path {A E V T : PointedSimplicialSet.{u}} {f g : A ⟶ E}
    (P : VerticalPath (PointedObject.toPoint E) f g) (i : T ⟶ A) (v : E ⟶ V) :
    ((P.basedPost v).pre i).path = ((P.pre i).basedPost v).path := by
  have h := (MonoidalClosed.pre i).naturality v
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at h
  change (P.path ≫ ((ihom A).map v).right) ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i V).right =
    (P.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i E).right) ≫ ((ihom T).map v).right
  simpa only [Under.comp_right, Category.assoc] using
    congrArg (fun q => P.path ≫ q.right) h

/-- 列射の同じ構造可換式は、実区間の後合成と構造像を厳密に交換する。 -/
lemma basedPost_sequence_step_path {Y Z : KanSequence.{u}} (p : KanSequence.Hom Y Z) (n : ℕ)
    {A : PointedSimplicialSet.{u}} {f g : A ⟶ (Y.level n).space}
    (P : VerticalPath (PointedObject.toPoint (Y.level n).space) f g) :
    ((P.basedPost (p.app n)).suspension.forgetProjection.basedPost (Z.sigma n)).path =
      ((P.suspension.forgetProjection.basedPost (Y.sigma n)).basedPost (p.app (n + 1))).path := by
  rw [suspension_basedPost_path]
  change (P.path ≫ ((ihom A).map (p.app n)).right) ≫
      (suspensionHom A (Z.level n).space ≫
        (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A)).map (Z.sigma n)).right =
    (P.path ≫ (suspensionHom A (Y.level n).space ≫
      (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A)).map (Y.sigma n)).right) ≫
        ((ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A)).map (p.app (n + 1))).right
  have h := RawSpectrumMapping.suspensionHom_post_pointed A (p.app n)
  have hm := congrArg (· ≫ (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A)).map (Z.sigma n)) h
  simp only [Category.assoc, ← Functor.map_comp] at hm
  rw [p.comm n] at hm
  simp only [Functor.map_comp] at hm
  simpa only [Under.comp_right, Category.assoc] using
    congrArg (fun q => P.path ≫ q.right) hm

end SerrePositivity.KST.Spectra.PointedMapping.VerticalPath
