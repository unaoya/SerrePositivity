module
public import SerrePositivity.KST.Fibration.VerdierSStageKernel
public import SerrePositivity.KST.Fibration.RelativeSCofiberCriterion

/-! # 元の S_n 包含の充満忠実性と実核像、その同じ cofiber による相対辺判定 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n : ℕ)
include h

/-- 元の Verdier 包含による S 後合成は、全写像空間で充満忠実。 -/
theorem verdierSPostcomp_fullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (sPostcomp n i.hom (exactMap_preservesSData i)) := by
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful
      (X := closedSubcategory (sClosedPredicate n (kernelClosedPredicate q)))
      (Y := sConstruction n B.obj)
      (closedStableInclusion (sClosedPredicate n (kernelClosedPredicate q))).val :=
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _
  have he := (verdierSStageKernelEquivalence h n).isFullyFaithful.comp hi
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (verdierSStageKernelEquivalence_inclusion h n)).mp he

/-- 元の S_n(D) の全図式は、元の同じ S 商作用で零になる。 -/
theorem verdierSPostcomp_image_isZero (a : (sConstruction n A.obj) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((sPostcomp n q.hom (exactMap_preservesSData q)).app (Opposite.op ⦋0⦌)
      ((sPostcomp n i.hom (exactMap_preservesSData i)).app (Opposite.op ⦋0⦌) a)) := by
  let k := (verdierSStageKernelEquivalence h n).hom.app (Opposite.op ⦋0⦌) a
  have hk := (sStageKernelPredicate_iff q n k.val).mp
    (closedSubcategory_vertex (sClosedPredicate n (kernelClosedPredicate q)) k)
  have he := congrArg (fun f : sConstruction n A.obj ⟶ sConstruction n B.obj =>
    f.app (Opposite.op ⦋0⦌) a) (verdierSStageKernelEquivalence_inclusion h n)
  exact (congrArg (fun z : (sConstruction n B.obj) _⦋0⦌ =>
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((sPostcomp n q.hom (exactMap_preservesSData q)).app
      (Opposite.op ⦋0⦌) z)) he).mp hk

/-- 同じ S 後合成の実核は、元の S_n(D) 包含の本質像と一致する。 -/
theorem verdierSPostcomp_kernel (v : (sConstruction n B.obj) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((sPostcomp n q.hom (exactMap_preservesSData q)).app
      (Opposite.op ⦋0⦌) v) ↔
      ∃ a : (sConstruction n A.obj) _⦋0⦌,
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := sConstruction n B.obj)
          ((sPostcomp n i.hom (exactMap_preservesSData i)).app (Opposite.op ⦋0⦌) a) v) := by
  constructor
  · intro hv
    let k : (closedSubcategory (sClosedPredicate n (kernelClosedPredicate q))) _⦋0⦌ :=
      ⟨v, by
        intro α
        have ha : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
        rw [ha, op_id, Functor.map_id_apply]
        exact (sStageKernelPredicate_iff q n v).mpr hv⟩
    obtain ⟨a, ⟨e⟩⟩ := (verdierSStageKernelEquivalence h n).isEssentiallySurjective k
    refine ⟨a, ⟨?_⟩⟩
    have he := congrArg (fun f : sConstruction n A.obj ⟶ sConstruction n B.obj =>
      f.app (Opposite.op ⦋0⦌) a) (verdierSStageKernelEquivalence_inclusion h n)
    exact (eqToIso (congrArg HomotopyCategory.mk he)).symm ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (closedStableInclusion (sClosedPredicate n (kernelClosedPredicate q))).val
  · rintro ⟨a, ⟨e⟩⟩
    exact (verdierSPostcomp_image_isZero h n a).of_vertexIso
      (e.map (sPostcomp n q.hom (exactMap_preservesSData q)))

/-- 相対 S_n 辺は、その同じ実 cofiber が元の S_n(D) 像に属する辺そのもの。 -/
theorem relativeSConstruction_mem_edge_iff_cofiber_image
    {x y : (sConstruction n B.obj) _⦋0⦌}
    {f : Truncated.Edge (X := (truncation 2).obj (sConstruction n B.obj)) x y}
    (s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare f) :
    f.edge ∈ (relativeSConstruction q.hom n).obj (Opposite.op ⦋1⦌) ↔
      ∃ a : (sConstruction n A.obj) _⦋0⦌,
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := sConstruction n B.obj)
          ((sPostcomp n i.hom (exactMap_preservesSData i)).app (Opposite.op ⦋0⦌) a) s.cofiber) :=
  (relativeSConstruction_mem_edge_iff_cofiber_zero h n s).trans
    (verdierSPostcomp_kernel h n s.cofiber)

end SerrePositivity.KST.Fibration
