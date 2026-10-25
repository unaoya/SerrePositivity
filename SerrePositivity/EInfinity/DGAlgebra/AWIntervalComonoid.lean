module

public import SerrePositivity.EInfinity.AlexanderWhitney.CochainComonoid
public import SerrePositivity.EInfinity.AlexanderWhitney.CochainVertices
public import SerrePositivity.EInfinity.IntervalCuts.CoalgebraInterval

/-!
概要：既存の正規化区間の両端点を AW 余モノイド射にする。
方針：単位の一における AW の頂点公式を使う。
規約：底の区間と端点は既存のものを保持する。
使われ方：dg 代数の実 path object の二端点評価。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.DGAlgebra
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
open scoped Simplicial TensorProduct
variable (R : Type u) [CommRing R]

/-- 概要：既存の端点は AW 対角を保つ。
方針：単位複体からの射を零次の一の像で比較する。
規約：両端点を同じ式で扱う。使われ方：余モノイド射の束ね。 -/
lemma intervalEndpoint_comul (b : Bool) :
    IntervalCuts.endpoint R b ≫ AlexanderWhitney.cochainDiagonal R Δ[1] =
      (λ_ (𝟙_ (Complex R))).inv ≫
        (IntervalCuts.endpoint R b ⊗ₘ IntervalCuts.endpoint R b) := by
  apply (complexSphereHomEquiv R _ 0).injective
  apply Subtype.ext
  change ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat R))).inv ≫
      (IntervalCuts.endpoint R b ≫ AlexanderWhitney.cochainDiagonal R Δ[1]).f 0) 1 =
    ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat R))).inv ≫
      ((λ_ (𝟙_ (Complex R))).inv ≫
        (IntervalCuts.endpoint R b ⊗ₘ IntervalCuts.endpoint R b)).f 0) 1
  simp only [comp_f, ModuleCat.comp_apply]
  erw [IntervalCuts.endpoint_zero_apply, one_smul]
  have hd := AlexanderWhitney.cochainDiagonal_vertex R (Δ[1] : SSet.{0})
    (IntervalCuts.vertexSimplex (if b then 1 else 0))
  have hv : IntervalCuts.faceVector R (IntervalCuts.vertex (if b then 1 else 0)) =
      (NegativeTensor.xIso (AlexanderWhitney.chains R Δ[1]) 0).inv
        (AlexanderWhitney.generator R Δ[1] 0
          (IntervalCuts.vertexSimplex (if b then 1 else 0))) := by
    simp only [IntervalCuts.faceVector, IntervalCuts.faceChain_vertex]
    rfl
  erw [hv, hd]
  erw [BarrattEccles.cochain_leftUnitor_inv_apply R]
  have ht := SerrePositivity.DifferentialGraded.ι_tensorHom (IntervalCuts.endpoint R b)
    (IntervalCuts.endpoint R b) 0 0 0 (show (0 : ℤ) + 0 = 0 from rfl)
  have hh := ConcreteCategory.congr_hom ht
    ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat R))).inv (1 : R) ⊗ₜ[R]
      (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat R))).inv (1 : R))
  simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul] at hh
  erw [IntervalCuts.endpoint_zero_apply, one_smul] at hh
  rw [← hv]
  exact hh.symm

/-- 概要：元の端点を単位余モノイドからの射に束ねる。
方針：既存の余単位三角形と上の対角保存を使う。
規約：底の射は endpoint 自身。使われ方：畳み込みの前合成。 -/
def intervalEndpointComon (b : Bool) :
    Comon.trivial (Complex R) ⟶ AlexanderWhitney.cochainComon R Δ[1] :=
  Comon.Hom.mk' (IntervalCuts.endpoint R b)
    (IntervalCuts.endpoint_contraction R b) (intervalEndpoint_comul R b)

/-- 概要：束ねた端点の底は元の端点。
方針：定義を読む。規約：定義上の一致。使われ方：既存の評価との照合。 -/
@[simp] lemma intervalEndpointComon_hom (b : Bool) :
    (intervalEndpointComon R b).hom = IntervalCuts.endpoint R b := rfl

end SerrePositivity.EInfinity.DGAlgebra
