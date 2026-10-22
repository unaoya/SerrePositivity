module
public import SerrePositivity.KST.Fibration.WeakStringGappedTranspose
public import SerrePositivity.KST.Fibration.FullSubcomplexJointReflection

/-! # 相対 S_n の元の単体から gapped W 列への逆向きの添字交換 -/

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

/-- 元の相対族を交換した各 Ar 頂点は、実際の W 列を表す。 -/
lemma relativeGappedWeakString_vertex {B C : StableCategory.{u}} (q : ExactMap B C)
    {n m : ℕ} (F : (Δ[m] : SSet.{u}) ⟶ (relativeSConstruction q.hom n : SSet.{u}))
    (a : (arNerve n) _⦋0⦌) :
    weakStringPredicate q ⦋m⦌
      ((internalHomFlipHomEquiv (Δ[m] : SSet.{u}) (arNerve n) B.obj
        (F ≫ (relativeSConstruction q.hom n).ι ≫ (gappedSubcomplex n B.obj).ι)).app
          (Opposite.op ⦋0⦌) a) := by
  let G : (Δ[m] : SSet.{u}) ⟶ diagramSpace n B.obj :=
    F ≫ (relativeSConstruction q.hom n).ι ≫ (gappedSubcomplex n B.obj).ι
  have he := flipFamily_vertex G a
  change q.hom.app _ (SSet.yonedaEquiv
    ((functorVertexEquiv (Δ[m] : SSet.{u}) B.obj).symm
      ((internalHomFlipHomEquiv _ _ _ G).app (Opposite.op ⦋0⦌) a))) ∈ _
  rw [he]
  exact (SSet.yonedaEquiv F).property a

/-- 元の相対 S_n 族を、同じ全 W 列図式圏に値を持つ Ar 図式に交換する。 -/
def relativeGappedWeakStringDiagram {B C : StableCategory.{u}} (q : ExactMap B C)
    {n m : ℕ} (F : (Δ[m] : SSet.{u}) ⟶ (relativeSConstruction q.hom n : SSet.{u})) :
    arNerve n ⟶ weakStringCategory q ⦋m⦌ :=
  fullSubcomplexLift (weakStringPredicate q ⦋m⦌)
    (internalHomFlipHomEquiv (Δ[m] : SSet.{u}) (arNerve n) B.obj
      (F ≫ (relativeSConstruction q.hom n).ι ≫ (gappedSubcomplex n B.obj).ι))
    (relativeGappedWeakString_vertex q F)

/-- 逆向きの交換を元の全関手圏へ含めると、同じ内部 Hom の交換を回収する。 -/
lemma relativeGappedWeakStringDiagram_ι {B C : StableCategory.{u}} (q : ExactMap B C)
    {n m : ℕ} (F : (Δ[m] : SSet.{u}) ⟶ (relativeSConstruction q.hom n : SSet.{u})) :
    relativeGappedWeakStringDiagram q F ≫
      (fullSubcomplexOnVertices _ (weakStringPredicate q ⦋m⦌)).ι =
        internalHomFlipHomEquiv (Δ[m] : SSet.{u}) (arNerve n) B.obj
          (F ≫ (relativeSConstruction q.hom n).ι ≫ (gappedSubcomplex n B.obj).ι) := rfl

/-- 逆向きに交換した元の Ar 図式は、全零対角と実押し出しを持つ。 -/
lemma relativeGappedWeakStringDiagram_isGapped {B C : StableCategory.{u}} (q : ExactMap B C)
    {n m : ℕ} (F : (Δ[m] : SSet.{u}) ⟶ (relativeSConstruction q.hom n : SSet.{u})) :
    IsGapped (relativeGappedWeakStringDiagram q F) := by
  apply IsGapped.of_fullSubcomplex (weakStringPredicate q ⦋m⦌)
  rw [relativeGappedWeakStringDiagram_ι]
  apply (isGapped_functor_iff_pointwise _).2
  intro k
  rw [flipFamily_evaluate]
  exact gappedDiagram_isGapped (F.app (Opposite.op ⦋0⦌) k).val

/-- 元の相対族を元の S_n(W 列) の頂点へ戻す、選択を加えない逆向きの写像。 -/
def relativeGappedWeakStringVertex {B C : StableCategory.{u}} (q : ExactMap B C)
    {n m : ℕ} (F : (Δ[m] : SSet.{u}) ⟶ (relativeSConstruction q.hom n : SSet.{u})) :
    (sConstruction n (weakStringCategory q ⦋m⦌)) _⦋0⦌ :=
  gappedObjectVertex (relativeGappedWeakStringDiagram q F)
    (relativeGappedWeakStringDiagram_isGapped q F)

end SerrePositivity.KST.Fibration
