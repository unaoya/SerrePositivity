module

public import SerrePositivity.KST.LocalizingInvariants.IdentityLaxDiagonal
public import SerrePositivity.KST.LocalizingInvariants.EquivalenceArrowFamily

/-!
概要：恒等 lax 差の真の核を、元の恒等矢印の対角の本質像に同定する。
方針：通常 pullback 上の可逆矢印族を始点固定の恒等族へ比較する。
規約：完全忠実性は元の全単体上の対角に対して証明する。使われ方：普遍の Verdier 列。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.IdentityLax
variable (Q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u})

lemma diagonal_fullyFaithful : IsFullyFaithful (diagonal Q) := by
  have hi : IsQCatEquivalence (equivalencePathRefl Q.obj ≫
      equivalencePathEndpoint Q.obj 0) := by
    rw [equivalencePathRefl_endpoint]
    exact (QCatEquivalence.refl Q.obj).isQCatEquivalence
  have hr := (isQCatEquivalence_of_trivialKanFibration
    (equivalencePathEndpoint Q.obj 0)).cancel_right hi
  have hc := hr.isFullyFaithful.comp
    (isFullyFaithful_fullSubcomplexOnVertices_ι _ IsEquivalencePathVertex)
  change IsFullyFaithful (equivalencePathRefl Q.obj ≫ equivalencePathι Q.obj) at hc
  rw [equivalencePathRefl_ι] at hc
  have he : IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.arrowLaxInverse Q.obj) :=
    (isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.arrowLaxIso Q.obj).inv).isFullyFaithful
  exact hc.comp he

def pullbackDiagonalIso : FunctorIso (pullbackInclusion (𝟙 Q) (𝟙 Q)).hom
    ((pullbackFst (𝟙 Q) (𝟙 Q)).hom ≫ diagonal Q) := by
  let j := F2.catPullbackToLax (𝟙 Q.obj) (𝟙 Q.obj)
  change FunctorIso j ((j ≫ F2.laxPullbackFst (𝟙 Q.obj) (𝟙 Q.obj)) ≫ diagonal Q)
  let a := j ≫ F2.laxPullbackArrow (𝟙 Q.obj) (𝟙 Q.obj)
  have ha : ∀ x, IsEquivalencePathVertex (a.app (Opposite.op ⦋0⦌) x) := by
    intro x
    exact F2.catPullbackToLax_vertex (𝟙 Q.obj) (𝟙 Q.obj) x
  have e := FunctorIso.postcomp (EquivalenceArrowFamily.comparison a ha)
    (_root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.arrowLaxInverse Q.obj)
  have hinv : F2.laxPullbackArrow (𝟙 Q.obj) (𝟙 Q.obj) ≫ _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.arrowLaxInverse Q.obj = 𝟙 _ :=
    (_root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.arrowLaxIso Q.obj).hom_inv_id
  have hsrc : a ≫ _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.arrowLaxInverse Q.obj = j := by
    rw [show a = j ≫ F2.laxPullbackArrow (𝟙 Q.obj) (𝟙 Q.obj) from rfl,
      Category.assoc, hinv, Category.comp_id]
  have hfst : a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      j ≫ F2.laxPullbackFst (𝟙 Q.obj) (𝟙 Q.obj) := by
    change (j ≫ F2.laxPullbackArrow (𝟙 Q.obj) (𝟙 Q.obj)) ≫ _ = _
    rw [Category.assoc, F2.laxPullbackArrow_source, Category.comp_id]
  rw [hsrc, hfst] at e
  simpa only [diagonal, Category.assoc] using e

lemma difference_kernel (x : (laxCategory (𝟙 Q) (𝟙 Q)).obj _⦋0⦌) :
    IsZeroVertex ((laxDifference (𝟙 Q) (𝟙 Q)).app (Opposite.op ⦋0⦌) x) ↔
      x ∈ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.essentialImage (exactDiagonal Q) := by
  constructor
  · intro hx
    obtain ⟨y, ⟨e⟩⟩ := (laxDifference_kernel (𝟙 Q) (𝟙 Q) x).mp hx
    exact ⟨(pullbackFst (𝟙 Q) (𝟙 Q)).hom.app (Opposite.op ⦋0⦌) y,
      ⟨((pullbackDiagonalIso Q).app y).symm ≪≫ e⟩⟩
  · rintro ⟨y, ⟨e⟩⟩
    exact (difference_diagonal_zero Q y).of_vertexIso (e.map (laxDifference (𝟙 Q) (𝟙 Q)))

end SerrePositivity.KST.LocalizingInvariants.IdentityLax
