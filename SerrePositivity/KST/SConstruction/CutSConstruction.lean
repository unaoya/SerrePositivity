module
public import SerrePositivity.KST.SConstruction.CutFamilyOperator
public import SerrePositivity.KST.SConstruction.SClosedFamilies
public import SerrePositivity.KST.SConstruction.SCofiberStableIso

/-! # S_n の内部の切断 cofiber 四角形
概要：切断を S_n C から S_n(cofiber C) への実際の単体的射にし、交換同型で S_n C 内へ戻す。
方針：各頂点の元の切断族を包含で照合し、gapped 性を全部分複体へ反映する。
規約：この射だけで Segal 同値を主張しない。使われ方：切断による相対比較の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 切断作用素の頂点が表す実図式は、包含後に元の切断四角形の族と一致する。 -/
lemma cutCofiberFamilyOperator_vertex_ι (n : ℕ) (k : Fin (n + 1)) (C : SSet.{u})
    [Quasicategory C] (v : (sConstruction n C) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) (cofiberDiagrams C)).symm
        ((cutCofiberFamilyOperator n k C).app (Opposite.op ⦋0⦌) v) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι =
        arCutFamily k (gappedDiagram v) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (cutCofiberFamilyOperator_ι n k C) (Opposite.op ⦋0⦌)) v
  exact (diagramVertex_postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι
    ((cutCofiberFamilyOperator n k C).app (Opposite.op ⦋0⦌) v)).symm.trans
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C)).symm
        (h.trans (cutRawFamilyOperator_vertex n k C v))).trans
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply _))

/-- 切断作用素は S_n C の各頂点を cofiber 図式値の gapped 図式に送る。 -/
lemma cutCofiberFamilyOperator_isGapped (n : ℕ) (k : Fin (n + 1)) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (v : (sConstruction n C) _⦋0⦌) :
    IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) (cofiberDiagrams C)).symm
      ((cutCofiberFamilyOperator n k C).app (Opposite.op ⦋0⦌) v)) := by
  apply IsGapped.of_fullSubcomplex IsCofiberDiagramVertex
  have h : IsGapped (arCutFamily k (gappedDiagram v)) := by
    have hg := (gappedCutCofiberFamily_isGapped k (gappedDiagram_isGapped v)).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι
      (cofiberInclusion_preservesSConstructionData C)
    exact hg
  exact (cutCofiberFamilyOperator_vertex_ι n k C v).symm ▸ h

/-- 同じ図式内の切断 cofiber 族を S_n(cofiber C) に送る実際の単体的射。 -/
def cutSConstructionMap (n : ℕ) (k : Fin (n + 1)) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] : sConstruction n C ⟶ sConstruction n (cofiberDiagrams C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (cutCofiberFamilyOperator n k C) (cutCofiberFamilyOperator_isGapped n k C)

/-- 切断の S_n への持ち上げは cofiber 族そのものを包含後に回収する。 -/
lemma cutSConstructionMap_ι (n : ℕ) (k : Fin (n + 1)) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    cutSConstructionMap n k C ≫ (gappedSubcomplex n (cofiberDiagrams C)).ι =
      cutCofiberFamilyOperator n k C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 切断の cofiber 族を転置し、S_n C の内部の cofiber 四角形にする。 -/
def cutCofiberComparison (n : ℕ) (k : Fin (n + 1)) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] : sConstruction n C ⟶ cofiberDiagrams (sConstruction n C) :=
  cutSConstructionMap n k C ≫ (sCofiberIso n C).hom

end SerrePositivity.KST.SConstruction
