module
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
概要：任意のアーベル圏で、負次数へ延長した鎖複体からの射と smart 切断への射を比較する。
方針：非正次数の始域の切断包含は同型なので、指定包含に対する一意な持ち上げを使う。
規約：零次数の閉元条件を保ち、図式圏にも適用できる。ホモロジーへの商は取らない。
使われ方：HA 1.2.4、G10 の図式圏で正規化した重みと Dold–Kan Hom の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits HomologicalComplex CochainComplex
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- 負次数埋め込みと零での smart 切断の埋め込みは同じ。 -/
theorem negativeEmbedding_eq :
    ComplexShape.embeddingDownNat = ComplexShape.embeddingUpIntLE 0 := by
  unfold ComplexShape.embeddingDownNat ComplexShape.embeddingUpIntLE ComplexShape.Embedding.mk'
  congr 1
  funext n
  exact (zero_sub (n : ℤ)).symm

/-- smart 切断の包含へ、非正次数の複体からの射を持ち上げる。 -/
def nonpositiveTruncationLift {F H : CochainComplex C ℤ} [F.IsStrictlyLE 0]
    (f : F ⟶ H) : F ⟶ H.truncLE 0 :=
  inv (F.ιTruncLE 0) ≫ CochainComplex.truncLEMap f 0

/-- 指定包含との合成は元の射そのもの。 -/
theorem nonpositiveTruncationLift_inclusion {F H : CochainComplex C ℤ} [F.IsStrictlyLE 0]
    (f : F ⟶ H) : nonpositiveTruncationLift f ≫ H.ιTruncLE 0 = f := by
  rw [nonpositiveTruncationLift, Category.assoc, CochainComplex.ιTruncLE_naturality,
    IsIso.inv_hom_id_assoc]

/-- 零での延長と smart 切断の、実際の射の同値。 -/
def zeroExtendTruncationHomEquiv (L : ChainComplex C ℕ) (H : CochainComplex C ℤ) :
    (L.extend (ComplexShape.embeddingUpIntLE 0) ⟶ H) ≃
      (L ⟶ H.truncLE' (ComplexShape.embeddingUpIntLE 0)) := by
  let e := ComplexShape.embeddingUpIntLE 0
  let F := e.extendFunctor C
  have : CochainComplex.IsStrictlyLE (F.obj L) 0 := by
    change (L.extend e).IsStrictlySupported e
    infer_instance
  let t := H.truncLEIso e
  have : Mono (H.ιTruncLE 0) := by
    change Mono (HomologicalComplex.ιTruncLE H e)
    infer_instance
  refine {
    toFun := fun f => F.preimage (nonpositiveTruncationLift f ≫ t.hom)
    invFun := fun g => F.map g ≫ t.inv ≫ H.ιTruncLE 0
    left_inv := ?_
    right_inv := ?_ }
  · intro f
    change F.map (F.preimage (nonpositiveTruncationLift f ≫ t.hom)) ≫ t.inv ≫ H.ιTruncLE 0 = f
    erw [Functor.map_preimage, Category.assoc, Iso.hom_inv_id_assoc,
      nonpositiveTruncationLift_inclusion]
  · intro g
    apply F.map_injective
    change F.map (F.preimage (nonpositiveTruncationLift _ ≫ t.hom)) = F.map g
    rw [Functor.map_preimage]
    apply (cancel_mono (t.inv ≫ H.ιTruncLE 0)).mp
    simp only [Category.assoc, Iso.hom_inv_id_assoc, nonpositiveTruncationLift_inclusion]

/-- 同じ埋め込みを明示的に同定したときの延長・切断 Hom 同値。 -/
def extendTruncationHomEquivOfEmbedding
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ))
    (he : e = ComplexShape.embeddingUpIntLE 0)
    (L : ChainComplex C ℕ) (H : CochainComplex C ℤ) :
    (L.extend e ⟶ H) ≃ (L ⟶ H.truncLE' (ComplexShape.embeddingUpIntLE 0)) := by
  subst e
  exact zeroExtendTruncationHomEquiv L H

/-- 負次数への零延長からの射を、同じ smart 切断への鎖射へ送る。 -/
def negativeExtendTruncationHomEquiv (L : ChainComplex C ℕ) (H : CochainComplex C ℤ) :
    (L.extend ComplexShape.embeddingDownNat ⟶ H) ≃
      (L ⟶ H.truncLE' (ComplexShape.embeddingUpIntLE 0)) :=
  extendTruncationHomEquivOfEmbedding _ negativeEmbedding_eq L H

end SerrePositivity.HomologicalAlgebra
