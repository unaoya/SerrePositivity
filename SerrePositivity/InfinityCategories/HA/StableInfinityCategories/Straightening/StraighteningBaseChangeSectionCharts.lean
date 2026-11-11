module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
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
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftFibrationBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningAllBases
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexDomains
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexFirstVertex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexFirstVertexNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexSectionBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexSectionDiagram
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.IsoEndpointNormalization
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.StraighteningBaseChangeRestriction

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening
open _root_.SerrePositivity.KST.Fibration
variable {B D : SSet.{u}} (k : D ⟶ B)

private lemma normalizeTriangle {C : Type v} [Category.{w} C]
    {a b s t s' t' : C} (l : a ≅ t) (e : s ≅ t) (r : b ≅ s)
    (hs : s = s') (ht : t = t') :
    l ≪≫ e.symm ≪≫ r.symm =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints l rfl ht ≪≫
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints e hs ht).symm ≪≫
          (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints r rfl hs).symm := by
  subst s' t'
  simp only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints, eqToIso_refl, Iso.refl_symm, Iso.refl_trans,
    Iso.trans_refl]

lemma mapNormalizeTriangle {C : Type v} [Category.{w} C]
    {Z : Type v'} [Category.{w'} Z] (F : C ⥤ Z) {a b s t : C} {s' t' : Z}
    (l : a ≅ t) (e : s ≅ t) (r : b ≅ s) (d : a ≅ b)
    (hd : d = l ≪≫ e.symm ≪≫ r.symm) (hs : F.obj s = s') (ht : F.obj t = t') :
    F.mapIso d = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints (F.mapIso l) rfl ht ≪≫
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints (F.mapIso e) hs ht).symm ≪≫
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints (F.mapIso r) rfl hs).symm := by
  subst d
  rw [Functor.mapIso_trans, Functor.mapIso_trans, Functor.mapIso_symm, Functor.mapIso_symm]
  exact normalizeTriangle _ _ _ hs ht

/-- 元の大域底変換の定義で使った、左側の切断図式への同じ比較。 -/
def straighteningJointBaseChangeLeftIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap D) ≫
        ((SSet.uliftFunctor.{u + 1, u}).map k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram B))
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor k)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity B) := by
  let U := SSet.uliftFunctor.{u + 1, u}
  let t := U.map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor k))
  let l := U.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap D)
  have hleft : l ≫ (U.map k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram B) =
      t ≫ (U.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram B) := by
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSimplexFirstVertexMap_ulift_naturality k, Category.assoc]
  exact eqToIso (congrArg (fun f => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) hleft) ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram_restrictIso B).precomp t

/-- 右側も元の制限同型そのものを使う。 -/
def straighteningJointBaseChangeRightIso :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram_restrictIso D).postcomp
    ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationInfinityBaseChange k)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

/-- 同じ指定制限同型を、元の左右の比較と元の逆切断比較へ厳密に分解する。 -/
theorem straighteningJointBaseChangeRestrictionIso_factor :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.straighteningJointBaseChangeRestrictionIso k =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.straighteningJointBaseChangeLeftIso k ≪≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity_baseChangeIso k).symm ≪≫
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.straighteningJointBaseChangeRightIso k).symm := by
  simp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.straighteningJointBaseChangeRestrictionIso, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.straighteningJointBaseChangeLeftIso,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.straighteningJointBaseChangeRightIso, Iso.trans_assoc]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.mapNormalizeTriangle := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.mapNormalizeTriangle

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.straighteningJointBaseChangeLeftIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.straighteningJointBaseChangeLeftIso := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.straighteningJointBaseChangeLeftIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.straighteningJointBaseChangeRestrictionIso_factor := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.straighteningJointBaseChangeRestrictionIso_factor

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.straighteningJointBaseChangeRightIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.straighteningJointBaseChangeRightIso := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.straighteningJointBaseChangeRightIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.straighteningJointBaseChangeLeftIso._proof_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.straighteningJointBaseChangeLeftIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.straighteningJointBaseChangeLeftIso._proof_2 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.straighteningJointBaseChangeLeftIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.straighteningJointBaseChangeLeftIso.eq_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.straighteningJointBaseChangeLeftIso.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.straighteningJointBaseChangeRightIso.eq_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.straighteningJointBaseChangeRightIso.eq_1
