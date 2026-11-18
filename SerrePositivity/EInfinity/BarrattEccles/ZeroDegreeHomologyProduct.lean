module

public import SerrePositivity.EInfinity.BarrattEccles.HomologyAlgebra
public import SerrePositivity.EInfinity.BarrattEccles.HomologyDiscreteComparison
public import SerrePositivity.HomologicalAlgebra.Complexes.HomologyZero.SingleValueMaps
public import SerrePositivity.HomologicalAlgebra.Complexes.HomologyZero.ZeroDegreeHomExt

/-!
# 標準 H⁰ 同型の実際の単位・積の保存

概要：零次集中 E 代数の標準 H⁰ 同型は元のホモロジー環の単位と積を保つ。
方針：任意の単位からの二代表で評価し、同じ pairingValue_class を使う。
規約：元の H⁰ 可換代数の離散像へ比較する。
使われ方：Com 全作用を保つ代数同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.HomologyZero
attribute [local implicit_reducible] SerrePositivity.TensorPowers.power
variable {A : Type u} [CommRing A]
variable (B : (operad A).Algebra) [B.carrier.IsStrictlyLE 0] [B.carrier.IsStrictlyGE 0]

lemma zeroDegreeToSingle_nullary :
    homologyOperation B 0 ≫ _root_.SerrePositivity.HomologyZero.zeroDegreeToSingle B.carrier =
      homologyOperation ((discreteAlgebraFunctor A).obj (homologyCommAlgebra B)) 0 := by
  apply _root_.SerrePositivity.HomologyZero.singleValue_injective (B.carrier.homology 0)
  rw [_root_.SerrePositivity.HomologyZero.zeroDegreeToSingle_unit_value, homologyNullary_discrete]
  let := homologyCommRing B
  let := homologyAlgebra B
  change _root_.SerrePositivity.HomologyZero.unitClass B.carrier (homologyOperation B 0) =
    _root_.SerrePositivity.HomologyZero.singleValue (B.carrier.homology 0)
      ((CochainComplex.singleFunctor (ModuleCat A) 0).map
        (ModuleCat.ofHom (Algebra.linearMap A (B.carrier.homology 0))))
  rw [← Category.id_comp ((CochainComplex.singleFunctor (ModuleCat A) 0).map _),
    _root_.SerrePositivity.HomologyZero.singleValue_map]
  change homologyOne B = algebraMap A (B.carrier.homology 0) 1
  exact (map_one (algebraMap A (B.carrier.homology 0))).symm

lemma zeroDegreeToSingle_binary :
    homologyBinary B ≫ _root_.SerrePositivity.HomologyZero.zeroDegreeToSingle B.carrier =
      (_root_.SerrePositivity.HomologyZero.zeroDegreeToSingle B.carrier ⊗ₘ _root_.SerrePositivity.HomologyZero.zeroDegreeToSingle B.carrier) ≫
        homologyBinary ((discreteAlgebraFunctor A).obj (homologyCommAlgebra B)) := by
  apply _root_.SerrePositivity.HomologyZero.zeroDegree_pairing_ext B.carrier B.carrier
  intro f g
  apply _root_.SerrePositivity.HomologyZero.singleValue_injective (B.carrier.homology 0)
  have hl : _root_.SerrePositivity.HomologyZero.unitPairing (homologyBinary B ≫ _root_.SerrePositivity.HomologyZero.zeroDegreeToSingle B.carrier) f g =
      _root_.SerrePositivity.HomologyZero.unitPairing (homologyBinary B) f g ≫ _root_.SerrePositivity.HomologyZero.zeroDegreeToSingle B.carrier := by
    simp only [_root_.SerrePositivity.HomologyZero.unitPairing, Category.assoc, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hl, _root_.SerrePositivity.HomologyZero.zeroDegreeToSingle_unit_value, homologyBinary_discrete]
  let := homologyCommRing B
  let := homologyAlgebra B
  have hr : _root_.SerrePositivity.HomologyZero.unitPairing ((_root_.SerrePositivity.HomologyZero.zeroDegreeToSingle B.carrier ⊗ₘ _root_.SerrePositivity.HomologyZero.zeroDegreeToSingle B.carrier) ≫
      ((CochainComplex.singleFunctor (ModuleCat A) 0).mapCommMon.obj
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.moduleCommMonoid A (homologyCommAlgebra B))).mon.mul) f g =
      _root_.SerrePositivity.HomologyZero.unitPairing (((CochainComplex.singleFunctor (ModuleCat A) 0).mapCommMon.obj
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.moduleCommMonoid A (homologyCommAlgebra B))).mon.mul)
        (f ≫ _root_.SerrePositivity.HomologyZero.zeroDegreeToSingle B.carrier) (g ≫ _root_.SerrePositivity.HomologyZero.zeroDegreeToSingle B.carrier) := by
    change (λ_ (𝟙_ (Complex A))).inv ≫ (f ⊗ₘ g) ≫ _ ≫ _ =
      (λ_ (𝟙_ (Complex A))).inv ≫ ((f ≫ _) ⊗ₘ (g ≫ _)) ≫ _
    rw [← tensorHom_comp_tensorHom]
    simp only [Category.assoc]
  erw [hr]
  change _root_.SerrePositivity.HomologyZero.unitClass B.carrier (_root_.SerrePositivity.HomologyZero.unitPairing (homologyBinary B) f g) =
    _root_.SerrePositivity.HomologyZero.singleValue (B.carrier.homology 0)
      (_root_.SerrePositivity.HomologyZero.unitPairing ((cochainSingleTensorIso _ _).hom ≫
        (CochainComplex.singleFunctor (ModuleCat A) 0).map
          (ModuleCat.ofHom (LinearMap.mul' A (B.carrier.homology 0))))
        (f ≫ _root_.SerrePositivity.HomologyZero.zeroDegreeToSingle B.carrier) (g ≫ _root_.SerrePositivity.HomologyZero.zeroDegreeToSingle B.carrier))
  rw [_root_.SerrePositivity.HomologyZero.singlePairing_value, _root_.SerrePositivity.HomologyZero.zeroDegreeToSingle_unit_value, _root_.SerrePositivity.HomologyZero.zeroDegreeToSingle_unit_value]
  exact (_root_.SerrePositivity.HomologyZero.pairingValue_class (homologyBinary B) f g).symm

end SerrePositivity.EInfinity.BarrattEccles
