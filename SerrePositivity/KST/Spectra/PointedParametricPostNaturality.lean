module

public import SerrePositivity.KST.Spectra.PointedParametricPost
public import SerrePositivity.KST.Spectra.PointedIhomActionSuspension

/-!
概要：標準の全族後合成の前後合成に関する自然性と、厳密な全族可換式の内部 Hom 像。
方針：元の ihomAction の豊穣自然性を転置し、同じ全族の射の等式へ戻す。
規約：Kan 性や充填選択を使わない。使われ方：元の随伴の全族可換式の二重 loop 像。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 同じ射の族へ源の射を前合成する操作は、内部 Hom に移した同じ射の前合成になる。 -/
lemma parametricPost_pre (K : PointedSimplicialSet.{u}) {P Y E F : PointedSimplicialSet.{u}}
    (a : Y ⟶ E) (w : P ⟶ PointedObject.basedHom E F) :
    parametricPost K (w ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a F) = PointedObject.basedHomMap K a ≫ parametricPost K w := by
  have hh := ihomAction_pre K a F
  change _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a F ≫ ihomAction K Y F = ihomAction K E F ≫
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.basedHomMap K a) (PointedObject.basedHom K F) at hh
  have h : (w ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a F) ≫ ihomAction K Y F =
      (w ≫ ihomAction K E F) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.basedHomMap K a) (PointedObject.basedHom K F) := by
    simpa only [Category.assoc] using congrArg (w ≫ ·) hh
  have ht := congrArg transpose h
  have hr := @transpose_pre_inner P (PointedObject.basedHom K E)
    (PointedObject.basedHom K Y) (PointedObject.basedHom K F)
    (w ≫ ihomAction K E F) (PointedObject.basedHomMap K a)
  exact ht.trans hr

/-- 同じ射の族へ標的の射を後合成する操作も、内部 Hom の同じ後合成になる。 -/
lemma parametricPost_post (K : PointedSimplicialSet.{u}) {P Y E F : PointedSimplicialSet.{u}}
    (v : P ⟶ PointedObject.basedHom Y E) (b : E ⟶ F) :
    parametricPost K (v ≫ PointedObject.basedHomMap Y b) =
      parametricPost K v ≫ PointedObject.basedHomMap P (PointedObject.basedHomMap K b) := by
  have hh := ihomAction_post K Y b
  change PointedObject.basedHomMap Y b ≫ ihomAction K Y F = ihomAction K Y E ≫
    PointedObject.basedHomMap (PointedObject.basedHom K Y) (PointedObject.basedHomMap K b) at hh
  have h : (v ≫ PointedObject.basedHomMap Y b) ≫ ihomAction K Y F =
      (v ≫ ihomAction K Y E) ≫
        PointedObject.basedHomMap (PointedObject.basedHom K Y) (PointedObject.basedHomMap K b) := by
    simpa only [Category.assoc] using congrArg (v ≫ ·) hh
  exact (congrArg transpose h).trans
    (transpose_post (v ≫ ihomAction K Y E) (PointedObject.basedHomMap K b))

/-- 厳密な全族可換式は、同じ標準内部 Hom 作用の厳密な全族可換式へ移る。 -/
lemma parametricPost_square (K : PointedSimplicialSet.{u})
    {P Y Y' E E' : PointedSimplicialSet.{u}} (a : Y ⟶ E) (a' : Y' ⟶ E')
    (v : P ⟶ PointedObject.basedHom Y Y') (w : P ⟶ PointedObject.basedHom E E')
    (hc : a ≫ transpose w = transpose v ≫ PointedObject.basedHomMap P a') :
    PointedObject.basedHomMap K a ≫ parametricPost K w =
      parametricPost K v ≫ PointedObject.basedHomMap P (PointedObject.basedHomMap K a') := by
  have h := congrArg transpose hc
  have hl := transpose_pre_outer (transpose w) a
  have hr := transpose_post (transpose v) a'
  rw [transpose_transpose] at hl hr
  have hf : w ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a E' = v ≫ PointedObject.basedHomMap Y a' :=
    hl.symm.trans (h.trans hr)
  have hk := congrArg (fun z => parametricPost K z) hf
  rw [parametricPost_pre, parametricPost_post] at hk
  exact hk

end SerrePositivity.KST.Spectra.PointedMapping
