module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMappingVertices
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
概要：指定底の実相対写像の零単体を、元の底を保つ代数射と同定する。
方針：元の pullback の両射影と AW 零単体同型を使う。
規約：底の式 f ≫ q = s は元の代数射の厳密な等式。
使われ方：固定底の導来写像空間比較の零単体での正規化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A X B : Mon (Complex R)}
  (q : X ⟶ B) (s : A ⟶ B)

lemma multiplicativeMappingBase_postcompose (f : A ⟶ X) :
    multiplicativeMappingBase R f ≫ multiplicativeMappingPostcompose R A q =
      multiplicativeMappingBase R (f ≫ q) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  change (f ≫ convolutionConstantMap R (simplexComonoid R n.unop) X) ≫
      (convolutionFunctor R (simplexComonoid R n.unop)).map q =
    (f ≫ q) ≫ convolutionConstantMap R (simplexComonoid R n.unop) B
  rw [Category.assoc, convolutionConstantMap_naturality, Category.assoc]

def relativeMultiplicativeMappingPoint (f : A ⟶ X) (hf : f ≫ q = s) :
    (Δ[0] : SSet.{u}) ⟶ relativeMultiplicativeMappingSimplices R q s :=
  pullback.lift (multiplicativeMappingBase R f) (𝟙 _) (by
    rw [multiplicativeMappingBase_postcompose, hf, Category.id_comp])

lemma relativeMultiplicativeMappingPoint_projection (f : A ⟶ X) (hf : f ≫ q = s) :
    relativeMultiplicativeMappingPoint R q s f hf ≫ relativeMultiplicativeMappingProjection R q s =
      multiplicativeMappingBase R f := pullback.lift_fst _ _ _

lemma relativeMultiplicativeMappingProjection_injective (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((relativeMultiplicativeMappingProjection R q s).app n) := by
  intro a b h
  apply Types.ext_of_isPullback
    (((evaluation SimplexCategoryᵒᵖ (Type u)).obj n).map_isPullback
      (IsPullback.of_hasPullback (multiplicativeMappingPostcompose R A q)
        (multiplicativeMappingBase R s))) h
  apply (SSet.yonedaEquiv.{u} (X := (Δ[0] : SSet.{u})) (n := n.unop)).symm.injective
  exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

def relativeMultiplicativeMappingVertex (f : A ⟶ X) (hf : f ≫ q = s) :
    (relativeMultiplicativeMappingSimplices R q s) _⦋0⦌ :=
  (relativeMultiplicativeMappingPoint R q s f hf).app (op ⦋0⦌)
    (SSet.yonedaEquiv.{u} (𝟙 (Δ[0] : SSet.{u})))

lemma relativeMultiplicativeMappingVertex_projection (f : A ⟶ X) (hf : f ≫ q = s) :
    (relativeMultiplicativeMappingProjection R q s).app (op ⦋0⦌)
      (relativeMultiplicativeMappingVertex R q s f hf) =
        multiplicativeMappingVertexEquiv R A X f := by
  have h := ConcreteCategory.congr_hom
    (congr_app (relativeMultiplicativeMappingPoint_projection R q s f hf) (op ⦋0⦌))
    (SSet.yonedaEquiv.{u} (𝟙 (Δ[0] : SSet.{u})))
  exact h

def relativeMultiplicativeMappingVertexDecode
    (z : (relativeMultiplicativeMappingSimplices R q s) _⦋0⦌) : A ⟶ X :=
  (multiplicativeMappingVertexEquiv R A X).symm
    ((relativeMultiplicativeMappingProjection R q s).app (op ⦋0⦌) z)

lemma relativeMultiplicativeMappingVertexDecode_over
    (z : (relativeMultiplicativeMappingSimplices R q s) _⦋0⦌) :
    relativeMultiplicativeMappingVertexDecode R q s z ≫ q = s := by
  apply (multiplicativeMappingVertexEquiv R A B).injective
  rw [← multiplicativeMappingVertexEquiv_postcompose]
  unfold relativeMultiplicativeMappingVertexDecode
  rw [Equiv.apply_symm_apply]
  exact relativeMultiplicativeMapping_condition_app R q s (op ⦋0⦌) z

def relativeMultiplicativeMappingVertexEquiv :
    {f : A ⟶ X // f ≫ q = s} ≃ (relativeMultiplicativeMappingSimplices R q s) _⦋0⦌ where
  toFun f := relativeMultiplicativeMappingVertex R q s f.val f.property
  invFun z := ⟨relativeMultiplicativeMappingVertexDecode R q s z,
    relativeMultiplicativeMappingVertexDecode_over R q s z⟩
  left_inv f := by
    apply Subtype.ext
    change relativeMultiplicativeMappingVertexDecode R q s
      (relativeMultiplicativeMappingVertex R q s f.val f.property) = f.val
    change (multiplicativeMappingVertexEquiv R A X).symm
      ((relativeMultiplicativeMappingProjection R q s).app (op ⦋0⦌)
        (relativeMultiplicativeMappingVertex R q s f.val f.property)) = f.val
    rw [relativeMultiplicativeMappingVertex_projection, Equiv.symm_apply_apply]
  right_inv z := by
    apply relativeMultiplicativeMappingProjection_injective R q s (op ⦋0⦌)
    rw [relativeMultiplicativeMappingVertex_projection]
    exact (multiplicativeMappingVertexEquiv R A X).apply_symm_apply _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
