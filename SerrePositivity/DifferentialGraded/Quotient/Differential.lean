module
public import SerrePositivity.DifferentialGraded.Quotient.ErasureSquare
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-! # 明示的dg商の最終Hom微分

全path直和の内部微分にε消去作用素を加える。内部微分との反交換と消去作用素の二乗零は
既に証明済みであり、条件を外部から仮定せずに非有界複体を構成する。
合成がこの微分と両立することは後続で検証する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits Preadditive MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 内部微分とε消去の和を微分とする、最終dg商のHom複体。 -/
def quotientHom (S : Set D) (x y : D) : Complex A :=
  perturbComplex (internalHom A D S x y) (erasure A D S x y)
    (erasure_closed A D S x y) (erasure_square_zero A D S x y)

@[simp] lemma quotientHom_X (S : Set D) (x y : D) (i : ℤ) :
    (quotientHom A D S x y).X i = (internalHom A D S x y).X i := rfl

@[simp] lemma quotientHom_d (S : Set D) (x y : D) (i : ℤ) :
    (quotientHom A D S x y).d i (i + 1) =
      (internalHom A D S x y).d i (i + 1) + (erasure A D S x y).v i (i + 1) rfl :=
  perturbComplex_d _ _ _ _ _

/-- 空pathの包含は最終微分に関してもchain mapとなる。 -/
def originalHomInclusion (S : Set D) (x y : D) :
    homObject A D x y ⟶ quotientHom A D S x y :=
  CochainComplex.ofHom (fun i => (originalHom A D S x y).f i) (fun i => by
    have hz : (originalHom A D S x y).f i ≫ (erasure A D S x y).v i (i + 1) rfl = 0 := by
      simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v] using
        congrArg (fun f : Cochain (homObject A D x y) (internalHom A D S x y) 1 =>
          f.v i (i + 1) rfl) (erasure_originalHom A D S x y)
    rw [quotientHom_d, comp_add, hz, add_zero]
    exact (originalHom A D S x y).comm i (i + 1))

@[simp] lemma originalHomInclusion_f (S : Set D) (x y : D) (i : ℤ) :
    (originalHomInclusion A D S x y).f i = (originalHom A D S x y).f i := rfl

/-- 空部分圏のとき消去作用素は全体で零。 -/
lemma erasure_empty (x y : D) : erasure A D ∅ x y = 0 := by
  apply pathCochain_ext A D ∅ x y 1
  intro w
  have hw := word_empty w
  subst w
  rw [erasure_precomp, eraseRow_nil, Cochain.comp_zero]

/-- 空部分圏を殺す最終Hom複体は、元のHom複体と同型である。 -/
def quotientHom_emptyIso (x y : D) : homObject A D x y ≅ quotientHom A D ∅ x y :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i).mapIso
      (emptyHomIso A D x y)) (fun i j hij => by
        change (originalHom A D ∅ x y).f i ≫ (quotientHom A D ∅ x y).d i j =
          (homObject A D x y).d i j ≫ (originalHom A D ∅ x y).f j
        change i + 1 = j at hij
        subst j
        rw [quotientHom_d, erasure_empty, Cochain.zero_v, add_zero]
        exact (originalHom A D ∅ x y).comm i (i + 1))

lemma quotientHom_emptyIso_hom (x y : D) :
    (quotientHom_emptyIso A D x y).hom = originalHomInclusion A D ∅ x y := by
  apply HomologicalComplex.Hom.ext
  funext i
  rfl

end SerrePositivity.DifferentialGraded.DGQuotient
