module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationBaseChange
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationInfinity
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningAllBases
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningBaseChange
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexDomains
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexFirstVertex
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexFirstVertexNaturality
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexSectionBaseChange
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexSectionDiagram
public import SerrePositivity.InfinityCategories.F1B.IsoEndpointNormalization
public import SerrePositivity.InfinityCategories.Stable.Straightening.StraighteningBaseChangeRestriction

/-!
分割で生成：docstring を書き直すこと
 # 元の大域底変換を、同じ切断空間への左右の指定比較で表示する
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w v' w'
open CategoryTheory Limits MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Stable.Straightening
open SerrePositivity.KST.Fibration
variable {B D : SSet.{u}} (k : D ⟶ B)

private lemma normalizeTriangle {C : Type v} [Category.{w} C]
    {a b s t s' t' : C} (l : a ≅ t) (e : s ≅ t) (r : b ≅ s)
    (hs : s = s') (ht : t = t') :
    l ≪≫ e.symm ≪≫ r.symm =
      F2.isoNormalizeEndpoints l rfl ht ≪≫
        (F2.isoNormalizeEndpoints e hs ht).symm ≪≫
          (F2.isoNormalizeEndpoints r rfl hs).symm := by
  subst s' t'
  simp only [F2.isoNormalizeEndpoints, eqToIso_refl, Iso.refl_symm, Iso.refl_trans,
    Iso.trans_refl]

lemma mapNormalizeTriangle {C : Type v} [Category.{w} C]
    {Z : Type v'} [Category.{w'} Z] (F : C ⥤ Z) {a b s t : C} {s' t' : Z}
    (l : a ≅ t) (e : s ≅ t) (r : b ≅ s) (d : a ≅ b)
    (hd : d = l ≪≫ e.symm ≪≫ r.symm) (hs : F.obj s = s') (ht : F.obj t = t') :
    F.mapIso d = F2.isoNormalizeEndpoints (F.mapIso l) rfl ht ≪≫
      (F2.isoNormalizeEndpoints (F.mapIso e) hs ht).symm ≪≫
        (F2.isoNormalizeEndpoints (F.mapIso r) rfl hs).symm := by
  subst d
  rw [Functor.mapIso_trans, Functor.mapIso_trans, Functor.mapIso_symm, Functor.mapIso_symm]
  exact normalizeTriangle _ _ _ hs ht

/-- 元の大域底変換の定義で使った、左側の切断図式への同じ比較。 -/
def straighteningJointBaseChangeLeftIso :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D) ≫
        ((SSet.uliftFunctor.{u + 1, u}).map k ≫ leftStraighteningSectionJointDiagram B))
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k)) ≫
        transportSimplexSectionInfinity B) := by
  let U := SSet.uliftFunctor.{u + 1, u}
  let t := U.map (nerveMap (transportSimplexFunctor k))
  let l := U.map (transportSimplexFirstVertexMap D)
  have hleft : l ≫ (U.map k ≫ leftStraighteningSectionJointDiagram B) =
      t ≫ (U.map (transportSimplexFirstVertexMap B) ≫
        leftStraighteningSectionJointDiagram B) := by
    rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k, Category.assoc]
  exact eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hleft) ≪≫
    (leftStraighteningSectionJointDiagram_restrictIso B).precomp t

/-- 右側も元の制限同型そのものを使う。 -/
def straighteningJointBaseChangeRightIso :=
  (leftStraighteningSectionJointDiagram_restrictIso D).postcomp
    ((pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u})

/-- 同じ指定制限同型を、元の左右の比較と元の逆切断比較へ厳密に分解する。 -/
theorem straighteningJointBaseChangeRestrictionIso_factor :
    _root_.SerrePositivity.InfinityCategories.Stable.Straightening.straighteningJointBaseChangeRestrictionIso k =
      _root_.SerrePositivity.InfinityCategories.Stable.Straightening.straighteningJointBaseChangeLeftIso k ≪≫
        (transportSimplexSectionInfinity_baseChangeIso k).symm ≪≫
          (_root_.SerrePositivity.InfinityCategories.Stable.Straightening.straighteningJointBaseChangeRightIso k).symm := by
  simp only [_root_.SerrePositivity.InfinityCategories.Stable.Straightening.straighteningJointBaseChangeRestrictionIso, _root_.SerrePositivity.InfinityCategories.Stable.Straightening.straighteningJointBaseChangeLeftIso,
    _root_.SerrePositivity.InfinityCategories.Stable.Straightening.straighteningJointBaseChangeRightIso, Iso.trans_assoc]

end SerrePositivity.InfinityCategories.Stable.Straightening

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.mapNormalizeTriangle := _root_.SerrePositivity.InfinityCategories.Stable.Straightening.mapNormalizeTriangle

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Straightening.straighteningJointBaseChangeLeftIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.straighteningJointBaseChangeLeftIso := _root_.SerrePositivity.InfinityCategories.Stable.Straightening.straighteningJointBaseChangeLeftIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.straighteningJointBaseChangeRestrictionIso_factor := _root_.SerrePositivity.InfinityCategories.Stable.Straightening.straighteningJointBaseChangeRestrictionIso_factor

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Straightening.straighteningJointBaseChangeRightIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.straighteningJointBaseChangeRightIso := _root_.SerrePositivity.InfinityCategories.Stable.Straightening.straighteningJointBaseChangeRightIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.straighteningJointBaseChangeLeftIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Straightening.straighteningJointBaseChangeLeftIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.straighteningJointBaseChangeLeftIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Stable.Straightening.straighteningJointBaseChangeLeftIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.straighteningJointBaseChangeLeftIso.eq_1 := _root_.SerrePositivity.InfinityCategories.Stable.Straightening.straighteningJointBaseChangeLeftIso.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.straighteningJointBaseChangeRightIso.eq_1 := _root_.SerrePositivity.InfinityCategories.Stable.Straightening.straighteningJointBaseChangeRightIso.eq_1
