module
public import SerrePositivity.KST.Fibration.RelativeGappedWeakString

/-! # 全 gapped W 列と相対 S 構成の実単体の選択を加えない同値 -/

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

/-- 元の gapped W 列を、元の相対 S_n に値を持つ実際の単体の族へ送る。 -/
def weakStringGappedRelativeMap {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n m : ℕ} (v : (sConstruction n (weakStringCategory q ⦋m⦌)) _⦋0⦌) :
    (Δ[m] : SSet.{u}) ⟶ (relativeSConstruction q.hom n : SSet.{u}) :=
  SSet.yonedaEquiv.symm (weakStringGappedRelativeSimplex q v)

/-- 元の相対包含は、同じ添字交換による全 gapped 族を回収する。 -/
@[reassoc]
lemma weakStringGappedRelativeMap_inclusion {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n m : ℕ} (v : (sConstruction n (weakStringCategory q ⦋m⦌)) _⦋0⦌) :
    weakStringGappedRelativeMap q v ≫ (relativeSConstruction q.hom n).ι =
      weakStringGappedTranspose q v := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp]
  change (SSet.yonedaEquiv (weakStringGappedRelativeMap q v)).val = _
  rw [weakStringGappedRelativeMap, Equiv.apply_symm_apply]
  rfl

/-- 零次数を含む全 n,m で、元の gapped W 列の対象と相対 S_n の実 m 単体が対応する。 -/
def weakStringGappedVerticesEquiv {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n m : ℕ) :
    (sConstruction n (weakStringCategory q ⦋m⦌)) _⦋0⦌ ≃
      ((Δ[m] : SSet.{u}) ⟶ (relativeSConstruction q.hom n : SSet.{u})) where
  toFun := weakStringGappedRelativeMap q
  invFun := relativeGappedWeakStringVertex q
  left_inv v := by
    apply gappedDiagram_injective
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q ⦋m⦌)).ι).1
    rw [relativeGappedWeakStringVertex, gappedDiagram_gappedObjectVertex,
      relativeGappedWeakStringDiagram_ι, ← Category.assoc,
      weakStringGappedRelativeMap_inclusion,
      weakStringGappedTranspose_ι]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (arNerve n) (Δ[m] : SSet.{u}) B.obj).left_inv _
  right_inv F := by
    apply (cancel_mono (relativeSConstruction q.hom n).ι).1
    apply (cancel_mono (gappedSubcomplex n B.obj).ι).1
    rw [weakStringGappedRelativeMap_inclusion, Category.assoc, weakStringGappedTranspose_ι]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (arNerve n) (Δ[m] : SSet.{u}) B.obj
      (gappedDiagram (relativeGappedWeakStringVertex q F) ≫ _) = _
    rw [relativeGappedWeakStringVertex, gappedDiagram_gappedObjectVertex,
      relativeGappedWeakStringDiagram_ι]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[m] : SSet.{u}) (arNerve n) B.obj).left_inv _

/-- 同じ対応を元の相対 S_n の実単体そのものに値を持つ同値として保持する。 -/
def weakStringGappedSimplexEquiv {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n m : ℕ) :
    (sConstruction n (weakStringCategory q ⦋m⦌)) _⦋0⦌ ≃
      (relativeSConstruction q.hom n : SSet.{u}) _⦋m⦌ :=
  (weakStringGappedVerticesEquiv q n m).trans SSet.yonedaEquiv

end SerrePositivity.KST.Fibration
