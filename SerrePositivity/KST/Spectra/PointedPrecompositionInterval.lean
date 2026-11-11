module

public import SerrePositivity.KST.Spectra.PointedRelativeTransposePaths

/-!
概要：同じ源比較の実区間を、内部 Hom の前合成の実区間へ移す。
方針：転置した普遍評価へ後合成し、同じ区間全体を再び転置する。
規約：区間を選び直さず Kan 性も不要。使われ方：実評価側の源単位区間の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 転置した普遍評価は、元の源比較による同じ前合成を表す。 -/
lemma transpose_evaluation_pre {W D : PointedSimplicialSet.{u}} (q : W ⟶ D)
    (C : PointedSimplicialSet.{u}) :
    transpose (q ≫ transpose (𝟙 (PointedObject.basedHom D C))) = _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed q C := by
  rw [transpose_pre_outer, transpose_transpose, Category.id_comp]

namespace VerticalPath

/-- 源の比較を変形する同じ実区間から、全内部 Hom の前合成を変形する区間を得る。 -/
def basedPre {W D : PointedSimplicialSet.{u}} {f g : W ⟶ D}
    (H : VerticalPath (PointedObject.toPoint D) f g) (C : PointedSimplicialSet.{u}) :
    VerticalPath (PointedObject.toPoint (PointedObject.basedHom W C))
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed f C) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed g C) :=
  ((H.basedPost (transpose (𝟙 (PointedObject.basedHom D C)))).basedTranspose).changeEndpoints
    (transpose_evaluation_pre f C).symm (transpose_evaluation_pre g C).symm

/-- 区間の源作用も、元の後合成・転置を通る同じ辺そのもの。 -/
lemma basedPre_path {W D : PointedSimplicialSet.{u}} {f g : W ⟶ D}
    (H : VerticalPath (PointedObject.toPoint D) f g) (C : PointedSimplicialSet.{u}) :
    (H.basedPre C).path =
      ((H.basedPost (transpose (𝟙 (PointedObject.basedHom D C)))).basedTranspose).path := rfl

/-- 元の源区間を前合成へ移し、指定した全パラメータの作用へ入力する。 -/
def basedPreAction {W D C A T : PointedSimplicialSet.{u}} {f g : W ⟶ D}
    (H : VerticalPath (PointedObject.toPoint D) f g)
    (r : A ⟶ PointedObject.basedHom D C) (a : T ⟶ A) :
    VerticalPath (PointedObject.toPoint (PointedObject.basedHom W C))
      (a ≫ r ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed f C) (a ≫ r ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed g C) :=
  ((H.basedPre C).pre r).pre a

end VerticalPath
end SerrePositivity.KST.Spectra.PointedMapping
