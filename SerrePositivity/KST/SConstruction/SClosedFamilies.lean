module
public import SerrePositivity.KST.SConstruction.SClosedPredicates
public import SerrePositivity.KST.SConstruction.CoreGappedFamilies
public import SerrePositivity.KST.SConstruction.FullSubcomplexGappedReflection

/-! # 閉じた全部分圏への S_n の族の持ち上げ
概要：各 Ar 成分が部分圏に入る S_n C の族を、S_n A の全高次単体の族として持ち上げる。
方針：内部 Hom の全部分複体表示で持ち上げ、gapped 性を包含後から反映する。
規約：object S だけの対応には縮めない。使われ方：S_n と閉じた全部分圏の交換同型。
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

/-- 内部 Hom の頂点が表す実図式は標的への後合成と可換。 -/
lemma diagramVertex_postcomp {A C D : SSet.{u}} (f : C ⟶ D)
    (v : ((ihom A).obj C) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A D).symm (((ihom A).map f).app (Opposite.op ⦋0⦌) v) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A C).symm v ≫ f := by
  obtain ⟨F, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A C).surjective v
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A D).symm_apply_apply (F ≫ f)

/-- 全 Ar 成分が部分圏に入る族を、部分圏を標的とする内部 Hom に持ち上げる。 -/
def sClosedDiagramLift {X : StableModel.{u}} (n : ℕ) (P : ClosedStablePredicate X)
    {K : SSet.{u}} (F : K ⟶ sConstruction n X.carrier)
    (hF : ∀ k : K _⦋0⦌, (sClosedPredicate n P).predicate (F.app (Opposite.op ⦋0⦌) k)) :
    K ⟶ (ihom (arNerve n)).obj (closedSubcategory P) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorVertexSatisfies (arNerve n) X.carrier P.predicate)
    (F ≫ (gappedSubcomplex n X.carrier).ι) hF ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexInternalHomBackward (arNerve n) X.carrier P.predicate

/-- 内部 Hom への持ち上げは元の Ar 図式の族を厳密に保持する。 -/
lemma sClosedDiagramLift_ι {X : StableModel.{u}} (n : ℕ) (P : ClosedStablePredicate X)
    {K : SSet.{u}} (F : K ⟶ sConstruction n X.carrier)
    (hF : ∀ k : K _⦋0⦌, (sClosedPredicate n P).predicate (F.app (Opposite.op ⦋0⦌) k)) :
    sClosedDiagramLift n P F hF ≫ (ihom (arNerve n)).map (closedStableInclusion P).val =
      F ≫ (gappedSubcomplex n X.carrier).ι := by
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (F ≫ (gappedSubcomplex n X.carrier).ι) hF ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexInternalHomBackward (arNerve n) X.carrier P.predicate ≫
          (ihom (arNerve n)).map (closedStableInclusion P).val) := Category.assoc _ _ _
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (F ≫ (gappedSubcomplex n X.carrier).ι) hF ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorVertexSatisfies (arNerve n) X.carrier P.predicate)).ι :=
      congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (F ≫ (gappedSubcomplex n X.carrier).ι) hF ≫ t)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexInternalHomBackward_ι (arNerve n) X.carrier P.predicate)
    _ = _ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorVertexSatisfies (arNerve n) X.carrier P.predicate)
      (F ≫ (gappedSubcomplex n X.carrier).ι) hF

/-- 持ち上げた各頂点の実図式は包含後に元の gapped 図式に一致する。 -/
lemma sClosedDiagramLift_vertex_ι {X : StableModel.{u}} (n : ℕ) (P : ClosedStablePredicate X)
    {K : SSet.{u}} (F : K ⟶ sConstruction n X.carrier)
    (hF : ∀ k : K _⦋0⦌, (sClosedPredicate n P).predicate (F.app (Opposite.op ⦋0⦌) k))
    (k : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) (closedSubcategory P)).symm
        ((sClosedDiagramLift n P F hF).app (Opposite.op ⦋0⦌) k) ≫
      (closedStableInclusion P).val = gappedDiagram (F.app (Opposite.op ⦋0⦌) k) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (sClosedDiagramLift_ι n P F hF) (Opposite.op ⦋0⦌)) k
  exact (diagramVertex_postcomp (closedStableInclusion P).val
    ((sClosedDiagramLift n P F hF).app (Opposite.op ⦋0⦌) k)).symm.trans
      (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) X.carrier).symm h)

/-- 全 Ar 成分の条件を持つ族は S_n A そのものに持ち上がる。 -/
def sClosedFamilyLift {X : StableModel.{u}} (n : ℕ) (P : ClosedStablePredicate X)
    {K : SSet.{u}} (F : K ⟶ sConstruction n X.carrier)
    (hF : ∀ k : K _⦋0⦌, (sClosedPredicate n P).predicate (F.app (Opposite.op ⦋0⦌) k)) :
    K ⟶ sConstruction n (closedSubcategory P) :=
  gappedFamilyLift (sClosedDiagramLift n P F hF) (by
    intro k
    apply IsGapped.of_fullSubcomplex P.predicate
    exact (sClosedDiagramLift_vertex_ι n P F hF k).symm ▸
      gappedDiagram_isGapped (F.app (Opposite.op ⦋0⦌) k))

/-- S_n A への持ち上げは元の完全な包含によって元の族に戻る。 -/
lemma sClosedFamilyLift_inclusion {X : StableModel.{u}} (n : ℕ) (P : ClosedStablePredicate X)
    {K : SSet.{u}} (F : K ⟶ sConstruction n X.carrier)
    (hF : ∀ k : K _⦋0⦌, (sClosedPredicate n P).predicate (F.app (Opposite.op ⦋0⦌) k)) :
    sClosedFamilyLift n P F hF ≫ ((sEndofunctor n).map (closedStableInclusion P)).val = F := by
  apply (cancel_mono (gappedSubcomplex n X.carrier).ι).1
  change _ ≫ (sPostcompCofiber n (closedStableInclusion P).val
    (closedStableInclusion P).property ≫ (gappedSubcomplex n X.carrier).ι) = _
  rw [sPostcompCofiber_ι, ← Category.assoc]
  have h : sClosedFamilyLift n P F hF ≫
      (gappedSubcomplex n (closedSubcategory P)).ι = sClosedDiagramLift n P F hF :=
    gappedFamilyLift_ι _ _
  exact (congrArg (fun t => t ≫ (ihom (arNerve n)).map (closedStableInclusion P).val) h).trans
    (sClosedDiagramLift_ι n P F hF)

end SerrePositivity.KST.SConstruction
