module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingNullCriterion
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.LocalFlatness
public import SerrePositivity.DifferentialGraded.Module.MaurerCartanTriangulated
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStableHomotopyEdges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedEdges

/-!
概要：元 cone が可縮な gluing 対象の元比較辺は可逆である。
方針：同じ実 cone の非輪状性から代表加群間の準同型性を得て Yoneda で反映する。
規約：比較辺の代表は変更しない。全関手の厳密逆は要求しない。
使われ方：V 上の全矢印族を Sp 正本の可逆矢印族比較に渡す。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories SSet
variable (R : Type u) [CommRing R] (C : Type (u + 1)) [DGCategory R C] [Small.{u} C]
local notation "I" => DGFunctor.id C
local notation "L" => DGIdentityHomGluing R C

/-- 概要：元 cone が可縮なら元閉比較射は H⁰ で可逆。
方針：同じ cone の零性を加群準同型性へ戻し、充満忠実 Yoneda で反映する。
規約：元射の H⁰ 類そのもの。使われ方：実可逆辺の認証。 -/
lemma dgIdentityHomGluingNullProperty_targetHomotopyIso (x : L)
    (hx : dgIdentityHomGluingNullProperty R C x) :
    IsIso ((toHomotopy R C).map (dgHomGluingTargetMap R C C C (I) (I) x)) := by
  let M := dgHomGluingTargetCone R C C C (I) (I) x
  obtain ⟨t, dt⟩ := hx
  have hz := DGQuotient.homotopy_isZero_of_unit_boundary R (RightModule R C) M.val t dt
  have hA : moduleAcyclic R C (ForgetEnrichment.of (Complex R) M.val) :=
    (moduleHomotopyAcyclic_obj_iff R C _).1
      ((moduleHomotopyAcyclic R C).prop_of_isZero hz)
  have hq := (moduleQuasiIso_iff_acyclic_cone R C
    (dgHomGluingTargetModuleMap R C C C (I) (I) x)).2 hA
  let Y := dgYoneda R C
  have hY (a b : C) : IsIso (Y.map a b) := by
    change IsIso (dgYonedaIso R a (representable R b)).inv
    infer_instance
  let : Y.onHomotopy.Full := Y.onHomotopy_full_of_homIso hY
  let : Y.onHomotopy.Faithful := Y.onHomotopy_faithful_of_homIso hY
  have hi : IsIso (Y.onHomotopy.map
      ((toHomotopy R C).map (dgHomGluingTargetMap R C C C (I) (I) x))) :=
    moduleHomotopicallyProjective_quasiIso_isIso_homotopy R C
      (representable_homotopicallyProjective R C x.left)
      (representable_homotopicallyProjective R C x.right) _ hq
  exact isIso_of_reflects_iso _ Y.onHomotopy

/-- 概要：元 cone 可縮対象の元の閉比較辺は native nerve 内で可逆。
方針：元 H⁰ の同型性を同じ native ホモトピー圏比較で反映する。
規約：辺代表を選び直さない。使われ方：V 上の可逆矢印全族の頂点条件。 -/
lemma dgIdentityHomGluingNullProperty_targetEdgeInvertible (x : L)
    (hx : dgIdentityHomGluingNullProperty R C x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R C (dgHomGluingTargetMap R C C C (I) (I) x)) := by
  have hi : IsIso ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R C).functor.map
      (Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R C (dgHomGluingTargetMap R C C C (I) (I) x)))) := by
    erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence_map_homMk, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_closed]
    exact dgIdentityHomGluingNullProperty_targetHomotopyIso R C x hx
  exact isIso_of_reflects_iso _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R C).functor

end SerrePositivity.KST.SConstruction
