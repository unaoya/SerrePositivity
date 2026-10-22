module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerHomologyLiftComposition
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovRoofCoefficientBimodules
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomologyInverseAfter

/-!
概要：元の π₂ の指定逆を、細分した共通底上の両層間の実 cochain 射に戻す。
方針：厳密 −2 集中と指定した元の係数同型を使い、元の両三角形を回収する。
規約：左右作用の保存は別証明。使われ方：双加群逆と元の class 比較の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  {k : ℕ} (hm : m ≤ k)

def postnikovRoofLayerInverse
    (r : (B.obj k).obj.X.homology (-2) ⟶ (A.obj i).obj.X.homology (-2)) :
    (postnikovOneRoofDenominatorLayer R f (postnikovOneRoofRefine R f c hm)).X ⟶
      (postnikovOneRoofNumeratorLayer R f (postnikovOneRoofRefine R f c hm)).X :=
  postnikovLayerHomologyLift R 1 r

lemma postnikovRoofLayerInverse_coefficient
    (r : (B.obj k).obj.X.homology (-2) ⟶ (A.obj i).obj.X.homology (-2)) :
    homologyMap (postnikovRoofLayerInverse R f c hm r) (-2) ≫
      (postnikovLayerHomologyIso R (A.obj i).obj 1).hom =
        (postnikovLayerHomologyIso R (B.obj k).obj 1).hom ≫ r :=
  postnikovLayerHomologyLift_coefficient R 1 r

lemma postnikovRoofLayerInverse_left
    (r : (B.obj k).obj.X.homology (-2) ⟶ (A.obj i).obj.X.homology (-2))
    (hl : homologyMap (f.app k).hom.hom (-2) ≫ r =
      homologyMap (A.transition (hi.trans hm)).hom.hom (-2)) :
    postnikovLayerMap R (f.app k).hom 1 ≫ postnikovRoofLayerInverse R f c hm r =
      postnikovLayerMap R (A.transition (hi.trans hm)).hom 1 :=
  postnikovLayerHomologyLift_left_triangle R 1 _ _ r hl

lemma postnikovRoofLayerInverse_right
    (r : (B.obj k).obj.X.homology (-2) ⟶ (A.obj i).obj.X.homology (-2))
    (hr : r ≫ homologyMap (f.app i).hom.hom (-2) =
      homologyMap (B.transition (hi.trans hm)).hom.hom (-2)) :
    postnikovRoofLayerInverse R f c hm r ≫ postnikovLayerMap R (f.app i).hom 1 =
      postnikovLayerMap R (B.transition (hi.trans hm)).hom 1 :=
  postnikovLayerHomologyLift_right_triangle R 1 _ _ r hr

lemma exists_postnikovRoofLayerInverse
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 2))) :
    ∃ k, ∃ hm : m ≤ k,
      ∃ r : (B.obj k).obj.X.homology (-2) ⟶ (A.obj i).obj.X.homology (-2),
      postnikovLayerMap R (f.app k).hom 1 ≫ postnikovRoofLayerInverse R f c hm r =
        postnikovLayerMap R (A.transition (hi.trans hm)).hom 1 ∧
      postnikovRoofLayerInverse R f c hm r ≫ postnikovLayerMap R (f.app i).hom 1 =
        postnikovLayerMap R (B.transition (hi.trans hm)).hom 1 := by
  let h := exists_nonpositiveHomologyInverse_after R f 2 hf i m
  let k := h.choose
  let hk : i ≤ k := h.choose_spec.choose
  have hs : m ≤ k ∧ ∃ r : (B.obj k).obj.X.homology (-2) ⟶ (A.obj i).obj.X.homology (-2),
      homologyMap (f.app k).hom.hom (-2) ≫ r = homologyMap (A.transition hk).hom.hom (-2) ∧
      r ≫ homologyMap (f.app i).hom.hom (-2) = homologyMap (B.transition hk).hom.hom (-2) :=
    h.choose_spec.choose_spec
  let r := hs.2.choose
  exact ⟨k, hs.1, r, postnikovRoofLayerInverse_left R f c hs.1 r hs.2.choose_spec.1,
    postnikovRoofLayerInverse_right R f c hs.1 r hs.2.choose_spec.2⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
