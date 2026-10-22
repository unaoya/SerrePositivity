module

public import SerrePositivity.EInfinity.BarrattEccles.HomologyAlgebra
public import SerrePositivity.EInfinity.BarrattEccles.HomologyDiscreteComparison
public import SerrePositivity.EInfinity.HomologyZero.SingleValueMaps
public import SerrePositivity.EInfinity.HomologyZero.ZeroDegreeHomExt

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
open SerrePositivity.DifferentialGraded HomologyZero
attribute [local implicit_reducible] SerrePositivity.TensorPowers.power
variable {A : Type u} [CommRing A]
variable (B : (operad A).Algebra) [B.carrier.IsStrictlyLE 0] [B.carrier.IsStrictlyGE 0]

lemma zeroDegreeToSingle_nullary :
    homologyOperation B 0 ≫ zeroDegreeToSingle B.carrier =
      homologyOperation ((discreteAlgebraFunctor A).obj (homologyCommAlgebra B)) 0 := by
  apply singleValue_injective (B.carrier.homology 0)
  rw [zeroDegreeToSingle_unit_value, homologyNullary_discrete]
  let := homologyCommRing B
  let := homologyAlgebra B
  change unitClass B.carrier (homologyOperation B 0) =
    singleValue (B.carrier.homology 0)
      ((CochainComplex.singleFunctor (ModuleCat A) 0).map
        (ModuleCat.ofHom (Algebra.linearMap A (B.carrier.homology 0))))
  rw [← Category.id_comp ((CochainComplex.singleFunctor (ModuleCat A) 0).map _),
    singleValue_map]
  change homologyOne B = algebraMap A (B.carrier.homology 0) 1
  exact (map_one (algebraMap A (B.carrier.homology 0))).symm

lemma zeroDegreeToSingle_binary :
    homologyBinary B ≫ zeroDegreeToSingle B.carrier =
      (zeroDegreeToSingle B.carrier ⊗ₘ zeroDegreeToSingle B.carrier) ≫
        homologyBinary ((discreteAlgebraFunctor A).obj (homologyCommAlgebra B)) := by
  apply zeroDegree_pairing_ext B.carrier B.carrier
  intro f g
  apply singleValue_injective (B.carrier.homology 0)
  have hl : unitPairing (homologyBinary B ≫ zeroDegreeToSingle B.carrier) f g =
      unitPairing (homologyBinary B) f g ≫ zeroDegreeToSingle B.carrier := by
    simp only [unitPairing, Category.assoc, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hl, zeroDegreeToSingle_unit_value, homologyBinary_discrete]
  let := homologyCommRing B
  let := homologyAlgebra B
  have hr : unitPairing ((zeroDegreeToSingle B.carrier ⊗ₘ zeroDegreeToSingle B.carrier) ≫
      ((CochainComplex.singleFunctor (ModuleCat A) 0).mapCommMon.obj
        (moduleCommMonoid A (homologyCommAlgebra B))).mon.mul) f g =
      unitPairing (((CochainComplex.singleFunctor (ModuleCat A) 0).mapCommMon.obj
        (moduleCommMonoid A (homologyCommAlgebra B))).mon.mul)
        (f ≫ zeroDegreeToSingle B.carrier) (g ≫ zeroDegreeToSingle B.carrier) := by
    change (λ_ (𝟙_ (Complex A))).inv ≫ (f ⊗ₘ g) ≫ _ ≫ _ =
      (λ_ (𝟙_ (Complex A))).inv ≫ ((f ≫ _) ⊗ₘ (g ≫ _)) ≫ _
    rw [← tensorHom_comp_tensorHom]
    simp only [Category.assoc]
  erw [hr]
  change unitClass B.carrier (unitPairing (homologyBinary B) f g) =
    singleValue (B.carrier.homology 0)
      (unitPairing ((cochainSingleTensorIso _ _).hom ≫
        (CochainComplex.singleFunctor (ModuleCat A) 0).map
          (ModuleCat.ofHom (LinearMap.mul' A (B.carrier.homology 0))))
        (f ≫ zeroDegreeToSingle B.carrier) (g ≫ zeroDegreeToSingle B.carrier))
  rw [singlePairing_value, zeroDegreeToSingle_unit_value, zeroDegreeToSingle_unit_value]
  exact (pairingValue_class (homologyBinary B) f g).symm

end SerrePositivity.EInfinity.BarrattEccles
