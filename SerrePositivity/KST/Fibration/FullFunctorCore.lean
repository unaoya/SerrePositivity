module
public import SerrePositivity.KST.Fibration.FunctorCoreCriterion
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexMapping

/-! # 全部分図式圏への商比較

商に写した図式が指定の全部分圏に入るとき、相対図式からその全部分圏の core へ
元の関手を保った射を構成する。gapped 図式への接続で使うが、その条件は仮定しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 全部分圏の core は周囲の core の厳密な逆像である。 -/
lemma fullSubcomplexCore_eq_preimage {Y : SSet.{u}} [Quasicategory Y]
    (P : Y _⦋0⦌ → Prop) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y P : SSet.{u}) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore Y).preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y P).ι := by
  ext n s
  change (∀ α : ⦋1⦌ ⟶ n.unop,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y P : SSet.{u}).map α.op s))) ↔ _
  constructor
  · intro hs α
    have hi := (hs α).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y P).ι
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y P : SSet.{u}).map α.op s)).map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y P).ι))
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (Y.map α.op s.val)) rfl).mp hi
  · intro hs α
    apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι Y P).reflects_isInvertibleEdge
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y P : SSet.{u}).map α.op s)).map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y P).ι))
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (Y.map α.op s.val)) rfl).mpr (hs α)

/-- 商図式が全部分圏に持ち上がる場合の、相対図式の正確な逆像表示。 -/
lemma relativeDiagram_eq_fullFunctorCore_preimage
    {K B C X : SSet.{u}} [Quasicategory C]
    (q : B ⟶ C) (d : X ⟶ (ihom K).obj B)
    (P : ((ihom K).obj C) _⦋0⦌ → Prop)
    (g : X ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom K).obj C) P : SSet.{u}))
    (hg : g ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom K).obj C) P).ι =
      d ≫ (ihom K).map q) :
    relativeDiagram q (fun k : K _⦋0⦌ => d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom K).obj C) P : SSet.{u})).preimage g := by
  rw [fullSubcomplexCore_eq_preimage, ← Subcomplex.preimage_comp, hg]
  exact relativeDiagram_eq_functorCore_preimage q d

/-- 指定全部分図式圏の core へ、元の商図式を保つ実射。 -/
def relativeDiagramFullFunctorCoreMap
    {K B C X : SSet.{u}} [Quasicategory C]
    (q : B ⟶ C) (d : X ⟶ (ihom K).obj B)
    (P : ((ihom K).obj C) _⦋0⦌ → Prop)
    (g : X ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom K).obj C) P : SSet.{u}))
    (hg : g ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom K).obj C) P).ι =
      d ≫ (ihom K).map q) :
    (relativeDiagram q (fun k : K _⦋0⦌ => d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k) : SSet.{u}) ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom K).obj C) P : SSet.{u}) :
        SSet.{u}) :=
  Subcomplex.lift ((relativeDiagram q (fun k => d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k)).ι ≫ g) (by
    rintro n _ ⟨s, rfl⟩
    have he := congrArg (fun T : X.Subcomplex => s.val ∈ T.obj n)
      (relativeDiagram_eq_fullFunctorCore_preimage q d P g hg)
    exact he.mp s.property)

/-- core への持ち上げの包含後は、指定した商図式そのもの。 -/
lemma relativeDiagramFullFunctorCoreMap_ι
    {K B C X : SSet.{u}} [Quasicategory C]
    (q : B ⟶ C) (d : X ⟶ (ihom K).obj B)
    (P : ((ihom K).obj C) _⦋0⦌ → Prop)
    (g : X ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom K).obj C) P : SSet.{u}))
    (hg : g ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom K).obj C) P).ι =
      d ≫ (ihom K).map q) :
    relativeDiagramFullFunctorCoreMap q d P g hg ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom K).obj C) P : SSet.{u})).ι =
      (relativeDiagram q (fun k : K _⦋0⦌ => d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k)).ι ≫ g := rfl

/-- 元の core 上では商の実関手の core 化そのものを回収する。 -/
lemma relativeDiagramFullFunctorCoreMap_core
    {K B C X : SSet.{u}} [Quasicategory C]
    (q : B ⟶ C) (d : X ⟶ (ihom K).obj B)
    (P : ((ihom K).obj C) _⦋0⦌ → Prop)
    (g : X ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom K).obj C) P : SSet.{u}))
    (hg : g ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom K).obj C) P).ι =
      d ≫ (ihom K).map q) :
    relativeDiagramCoreInclusion q (fun k : K _⦋0⦌ => d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k) ≫
      relativeDiagramFullFunctorCoreMap q d P g hg = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap g := by
  apply (cancel_mono
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom K).obj C) P : SSet.{u})).ι).1
  rw [Category.assoc, relativeDiagramFullFunctorCoreMap_ι, ← Category.assoc,
    relativeDiagramCoreInclusion_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι]

/-- 全部分圏を含めると、周囲の関手圏への同じ商比較を回収する。 -/
lemma relativeDiagramFullFunctorCoreMap_ambient
    {K B C X : SSet.{u}} [Quasicategory C]
    (q : B ⟶ C) (d : X ⟶ (ihom K).obj B)
    (P : ((ihom K).obj C) _⦋0⦌ → Prop)
    (g : X ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom K).obj C) P : SSet.{u}))
    (hg : g ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom K).obj C) P).ι =
      d ≫ (ihom K).map q) :
    relativeDiagramFullFunctorCoreMap q d P g hg ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom K).obj C) P).ι =
        relativeDiagramFunctorCoreMap q d := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom K).obj C)).ι).1
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι, ← Category.assoc,
    relativeDiagramFullFunctorCoreMap_ι, Category.assoc, hg,
    relativeDiagramFunctorCoreMap_ι]

end SerrePositivity.KST.Fibration
