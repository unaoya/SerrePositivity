module

public import SerrePositivity.EInfinity.BarrattEccles.ZeroTruncation
public import SerrePositivity.EInfinity.BarrattEccles.HomologyCoefficient
public import SerrePositivity.HomologicalAlgebra.Complexes.HomologyZero.TruncationRigidity
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Symmetric

/-!
# 零次集中 E 代数の全作用の augmentation 分解

概要：元の全 E 作用は同じ実 augmentation と切断後の作用の合成に厳密に一致する。
方針：実収縮の全ホモトピーを作用へ移し、支持の剛性で厳密な等式へ戻す。
規約：全 arity と元の作用を保持する。
使われ方：零次集中 E 代数を通常の可換代数と同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A] (B : (operad A).Algebra)

def zeroDegreeComAction (n : ℕ) : 𝟙_ (Complex A) ⊗ power B.carrier n ⟶ B.carrier :=
  (aritySection A n ▷ power B.carrier n) ≫ B.action n

lemma zeroDegreeAction_factor [B.carrier.IsStrictlyLE 0] [B.carrier.IsStrictlyGE 0] (n : ℕ) :
    ((augmentation A).map.app (FiniteBijection.of n) ▷ power B.carrier n) ≫
      zeroDegreeComAction B n = B.action n := by
  have : (complex A n).IsStrictlyLE 0 := arity_nonpositive A n
  have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.power_nonpositive B.carrier n
  have := KST.LocalizingInvariants.ConnectiveLift.tensor_nonpositive
    (complex A n) (power B.carrier n)
  have ht := SerrePositivity.cochainTensorHomotopyLeft
    (complexContraction A n).homotopyHomInvId (𝟙 (power B.carrier n))
  change _root_.Homotopy
    (((complexContraction A n).hom ≫ (complexContraction A n).inv) ⊗ₘ
      𝟙 (power B.carrier n))
    (𝟙 ((operad A).arity n) ⊗ₘ 𝟙 (power B.carrier n)) at ht
  have hs : (cochainTensor (complex A n) (power B.carrier n)).IsStrictlyLE 0 := by
    simpa only [add_zero] using cochainTensor_isStrictlyLE
      (complex A n) (power B.carrier n) 0 0
  have ht' := ht.compRight (B.action n)
  have he := _root_.SerrePositivity.HomologyZero.nonpositive_nonnegative_homotopy_eq ht'
  change (((augmentation A).map.app (FiniteBijection.of n) ≫ aritySection A n) ▷
    power B.carrier n) ≫ B.action n =
      (𝟙 ((operad A).arity n) ⊗ₘ 𝟙 (power B.carrier n)) ≫ B.action n at he
  simpa only [zeroDegreeComAction, tensorHom_id, comp_whiskerRight, Category.assoc,
    id_whiskerRight, Category.id_comp] using he

end SerrePositivity.EInfinity.BarrattEccles
