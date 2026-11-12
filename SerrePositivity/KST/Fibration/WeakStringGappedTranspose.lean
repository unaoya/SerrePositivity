module
public import SerrePositivity.KST.Fibration.WeakStringFiniteAllLengths
public import SerrePositivity.KST.Fibration.RelativeSConstruction
public import SerrePositivity.KST.SConstruction.CoreGappedFamilies

/-! # 元の gapped W 列を相対 S 構成の実単体へ交換する

局所化圏の射の等式を実現の比較と同一視せず、元の Ar と単体の添字を交換する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 元の gapped W 列を全関手圏へ含め、Ar と列の添字を交換した同じ族。 -/
def weakStringGappedTransposeRaw {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n m : ℕ} (v : (sConstruction n (weakStringCategory q ⦋m⦌)) _⦋0⦌) :
    (Δ[m] : SSet.{u}) ⟶ diagramSpace n B.obj :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (arNerve n) (Δ[m] : SSet.{u}) B.obj
    (gappedDiagram v ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q ⦋m⦌)).ι)

/-- 交換した元の族の全頂点は、元の完全包含と点ごとの普遍性により gapped。 -/
lemma weakStringGappedTranspose_vertex {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n m : ℕ} (v : (sConstruction n (weakStringCategory q ⦋m⦌)) _⦋0⦌)
    (k : (Δ[m] : SSet.{u}) _⦋0⦌) :
    IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) B.obj).symm
      ((weakStringGappedTransposeRaw q v).app (Opposite.op ⦋0⦌) k)) := by
  let F : arNerve n ⟶ (ihom (Δ[m] : SSet.{u})).obj B.obj :=
    gappedDiagram v ≫ (closedStableInclusion (weakStringClosedPredicate q ⦋m⦌)).val
  have hF : IsGapped F := (gappedDiagram_isGapped v).postcomp _
    (closedSubcategoryInclusion_preservesSConstructionData (weakStringClosedPredicate q ⦋m⦌))
  have he := flipFamily_vertex (A := arNerve n) (B := (Δ[m] : SSet.{u})) F k
  exact (congrArg IsGapped he).mpr ((isGapped_functor_iff_pointwise F).1 hF k)

/-- 交換した元の族は、元の全 gapped S_n(B) に値を持つ実際の射。 -/
def weakStringGappedTranspose {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n m : ℕ} (v : (sConstruction n (weakStringCategory q ⦋m⦌)) _⦋0⦌) :
    (Δ[m] : SSet.{u}) ⟶ sConstruction n B.obj :=
  gappedFamilyLift (weakStringGappedTransposeRaw q v) (weakStringGappedTranspose_vertex q v)

/-- 元の gapped 包含で戻すと、同じ内部 Hom の交換を厳密に回収する。 -/
@[reassoc]
lemma weakStringGappedTranspose_ι {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n m : ℕ} (v : (sConstruction n (weakStringCategory q ⦋m⦌)) _⦋0⦌) :
    weakStringGappedTranspose q v ≫ (gappedSubcomplex n B.obj).ι =
      weakStringGappedTransposeRaw q v := gappedFamilyLift_ι _ _

/-- 各元の Ar 成分の実 m 単体は、商に写すと core に入る。 -/
lemma weakStringGappedTranspose_relative {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n m : ℕ} (v : (sConstruction n (weakStringCategory q ⦋m⦌)) _⦋0⦌) :
    SSet.yonedaEquiv (weakStringGappedTranspose q v) ∈
      (relativeSConstruction q.hom n).obj (Opposite.op ⦋m⦌) := by
  intro a
  rw [← SSet.yonedaEquiv_comp]
  change SSet.yonedaEquiv
    ((weakStringGappedTranspose q v ≫ (gappedSubcomplex n B.obj).ι) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a ≫ q.hom) ∈ _
  rw [weakStringGappedTranspose_ι, weakStringGappedTransposeRaw, ← Category.assoc,
    flipFamily_evaluate, SSet.yonedaEquiv_comp]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex ((gappedDiagram v).app (Opposite.op ⦋0⦌) a)

/-- 元の全 gapped W 列から得た、wS_n(B) の実 m 単体。 -/
def weakStringGappedRelativeSimplex {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n m : ℕ} (v : (sConstruction n (weakStringCategory q ⦋m⦌)) _⦋0⦌) :
    (relativeSConstruction q.hom n : SSet.{u}) _⦋m⦌ :=
  ⟨SSet.yonedaEquiv (weakStringGappedTranspose q v), weakStringGappedTranspose_relative q v⟩

end SerrePositivity.KST.Fibration
