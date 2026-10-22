module

public import SerrePositivity.KST.LocalizingInvariants.CochainConnectiveLift
public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# 非負鎖複体の負次数延長と smart 切断の実 Hom 同値

概要：負次数へ延長した鎖複体からの射は、標的の smart 切断への元の鎖射と同値。
方針：切断への一意な持ち上げと元の延長関手の充満忠実性を使う。
規約：零次数の閉元条件を保持し、ホモロジーへ商を取らない。
使われ方：複体の frame Hom と実 Dold–Kan Hom の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory HomologicalComplex CochainComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.KST.LocalizingInvariants
variable {A : Type u} [CommRing A]

def extendTruncationHomEquiv (L : ChainComplex (ModuleCat.{u} A) ℕ) (H : Complex A) :
    (L.extend (ComplexShape.embeddingUpIntLE 0) ⟶ H) ≃
      (L ⟶ H.truncLE' (ComplexShape.embeddingUpIntLE 0)) := by
  let e := ComplexShape.embeddingUpIntLE 0
  let F := e.extendFunctor (ModuleCat A)
  have : CochainComplex.IsStrictlyLE (F.obj L) 0 := by
    change (L.extend e).IsStrictlySupported e
    infer_instance
  let t := H.truncLEIso e
  have : Mono (H.ιTruncLE 0) := by
    change Mono (HomologicalComplex.ιTruncLE H e)
    infer_instance
  refine {
    toFun := fun f => F.preimage (ConnectiveLift.lift f ≫ t.hom)
    invFun := fun g => F.map g ≫ t.inv ≫ H.ιTruncLE 0
    left_inv := ?_
    right_inv := ?_ }
  · intro f
    change F.map (F.preimage (ConnectiveLift.lift f ≫ t.hom)) ≫ t.inv ≫ H.ιTruncLE 0 = f
    erw [Functor.map_preimage, Category.assoc, Iso.hom_inv_id_assoc, ConnectiveLift.lift_inclusion]
  · intro g
    apply F.map_injective
    change F.map (F.preimage (ConnectiveLift.lift _ ≫ t.hom)) = F.map g
    rw [Functor.map_preimage]
    apply (cancel_mono (t.inv ≫ H.ιTruncLE 0)).mp
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ConnectiveLift.lift_inclusion]

end SerrePositivity.EInfinity.ComplexLimits
