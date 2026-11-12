module
public import SerrePositivity.KST.Fibration.WeakStringGappedVerticesEquiv

/-! # 元の gapped W 列と相対 S 単体の交換の両方向の厳密自然性 -/

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

/-- 元の相対 S の単体作用素は、包含の後に元の gapped 制限を回収する。 -/
@[reassoc]
lemma relativeSMap_inclusion {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {l n : ℕ} (θ : ⦋l⦌ ⟶ ⦋n⦌) :
    (relativeSimplicialSConstruction q.hom).map θ.op ≫ (relativeSConstruction q.hom l).ι =
      (relativeSConstruction q.hom n).ι ≫ sMap B.obj θ.toOrderHom :=
  (relativeSimplicialSConstructionInclusion q.hom).naturality θ.op

/-- 元の交換は、全ての Ar の面・退化の制限と厳密に可換。 -/
lemma weakStringGappedRelativeMap_sMap {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {l n m : ℕ} (θ : ⦋l⦌ ⟶ ⦋n⦌)
    (v : (sConstruction n (weakStringCategory q ⦋m⦌)) _⦋0⦌) :
    weakStringGappedRelativeMap q
      ((sMap (weakStringCategory q ⦋m⦌) θ.toOrderHom).app (Opposite.op ⦋0⦌) v) =
      weakStringGappedRelativeMap q v ≫ (relativeSimplicialSConstruction q.hom).map θ.op := by
  apply (cancel_mono (relativeSConstruction q.hom l).ι).1
  apply (cancel_mono (gappedSubcomplex l B.obj).ι).1
  simp only [Category.assoc, weakStringGappedRelativeMap_inclusion_assoc,
    relativeSMap_inclusion_assoc, sMap_ι, weakStringGappedRelativeMap_inclusion,
    weakStringGappedTranspose_ι]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (arNerve l) (Δ[m] : SSet.{u}) B.obj
    (gappedDiagram ((sMap _ θ.toOrderHom).app _ v) ≫ _) = _
  rw [gappedDiagram_sMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre,
    weakStringGappedTranspose_ι_assoc]
  rfl

/-- 元の交換は、W 列の全ての面・退化の制限とも厳密に可換。 -/
lemma weakStringGappedRelativeMap_reindex {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n l m : ℕ} (θ : ⦋l⦌ ⟶ ⦋m⦌)
    (v : (sConstruction n (weakStringCategory q ⦋m⦌)) _⦋0⦌) :
    weakStringGappedRelativeMap q
      (((sEndofunctor n).map (weakStringExactMap q θ)).val.app (Opposite.op ⦋0⦌) v) =
      stdSimplex.map θ ≫ weakStringGappedRelativeMap q v := by
  apply (cancel_mono (relativeSConstruction q.hom n).ι).1
  apply (cancel_mono (gappedSubcomplex n B.obj).ι).1
  simp only [Category.assoc, weakStringGappedRelativeMap_inclusion,
    weakStringGappedTranspose_ι]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (arNerve n) (Δ[l] : SSet.{u}) B.obj
    (gappedDiagram ((sPostcompCofiber n (weakStringMap q θ)
      (weakStringMap_preservesCofiberData q θ)).app _ v) ≫ _) = _
  rw [gappedDiagram_sPostcompCofiber, Category.assoc, weakStringMap_ι,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app]
  rfl

end SerrePositivity.KST.Fibration
