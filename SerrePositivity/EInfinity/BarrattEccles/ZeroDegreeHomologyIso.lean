module

public import SerrePositivity.EInfinity.BarrattEccles.ZeroDegreeHomologyProduct
public import SerrePositivity.EInfinity.BarrattEccles.ZeroDegreeComAlgebra
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CommutativeMonoidOperations

/-!
# 零次集中 E 代数と同じ H⁰ の離散像の代数同型

概要：標準 H⁰ 複体同型は Com と E の全 arity の代数同型になる。
方針：元の単位・積の保存から Com 射を構成し、実 augmentation へ制限する。
規約：比較先は既存 homologyCommAlgebra の既存離散関手の像。
使われ方：離散対象の本質像の逆包含。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.HomologyZero _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra
variable (A : Type u) [CommRing A]
variable (B : (operad A).Algebra) [B.carrier.IsStrictlyLE 0] [B.carrier.IsStrictlyGE 0]

def zeroDegreeHomologyComHom :
    zeroDegreeComAlgebra A B ⟶ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.discreteCommutativeFunctor A).obj (homologyCommAlgebra B) := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.commutativeHomOfUnitBinary _ _ (_root_.SerrePositivity.HomologyZero.zeroDegreeToSingle B.carrier)
  · change homologyOperation B 0 ≫ _root_.SerrePositivity.HomologyZero.zeroDegreeToSingle B.carrier =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.commutativeUnit (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeAlgebraOfMonoid
        (((CochainComplex.singleFunctor (ModuleCat A) 0).mapCommMon.obj
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.moduleCommMonoid A (homologyCommAlgebra B))).X))
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.commutativeUnit_ofMonoid]
    exact (zeroDegreeToSingle_nullary B).trans (homologyNullary_discrete A _)
  · change homologyBinary B ≫ _root_.SerrePositivity.HomologyZero.zeroDegreeToSingle B.carrier =
      (_root_.SerrePositivity.HomologyZero.zeroDegreeToSingle B.carrier ⊗ₘ _root_.SerrePositivity.HomologyZero.zeroDegreeToSingle B.carrier) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.commutativeBinary (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeAlgebraOfMonoid
          (((CochainComplex.singleFunctor (ModuleCat A) 0).mapCommMon.obj
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.moduleCommMonoid A (homologyCommAlgebra B))).X))
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.commutativeBinary_ofMonoid]
    rw [← homologyBinary_discrete]
    exact zeroDegreeToSingle_binary B

def zeroDegreeHomologyComIso :
    zeroDegreeComAlgebra A B ≅ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.discreteCommutativeFunctor A).obj (homologyCommAlgebra B) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.isoOfCarrierIso
    (X := zeroDegreeComAlgebra A B)
    (Y := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.discreteCommutativeFunctor A).obj (homologyCommAlgebra B))
    (_root_.SerrePositivity.HomologyZero.zeroDegreeHomologyIso B.carrier) (zeroDegreeHomologyComHom A B).comm

def zeroDegreeHomologyAlgebraIso :
    B ≅ (discreteAlgebraFunctor A).obj (homologyCommAlgebra B) :=
  (zeroDegreeComRestrictionIso A B).symm ≪≫
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.restrictAlgebra (augmentation A)).mapIso (zeroDegreeHomologyComIso A B)

end SerrePositivity.EInfinity.BarrattEccles
