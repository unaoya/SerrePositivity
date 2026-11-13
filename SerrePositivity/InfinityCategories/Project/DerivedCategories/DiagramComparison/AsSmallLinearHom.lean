module
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Linear.FunctorCategory
/-!
概要：AsSmall.downの前合成で同じ図式Homの全次数を移す。
方針：各コチェイン成分をdownで制限し、upで元の成分へ戻す。
規約：IS-W2 A12のΓ Homの添字照合の証明分割。任意の同値を選ばない。
使われ方：HA 1.2.4、元のBK Homの二重反対圏から持ち上げ添字への接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex CochainComplex HomComplex
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]
local notation "F" => Functor.obj (Functor.whiskeringLeft (AsSmall J) J (ModuleCat A)) AsSmall.down
/-- 元の図式複体の同じdown前合成。 -/
def asSmallComplexRestriction :
    CochainComplex (J ⥤ ModuleCat.{u} A) ℤ ⥤ CochainComplex (AsSmall.{u} J ⥤ ModuleCat.{u} A) ℤ :=
  ((Functor.whiskeringLeft (AsSmall.{u} J) J (ModuleCat A)).obj AsSmall.down).mapHomologicalComplex (.up ℤ)
/-- 全次数コチェインの同じup・downによる線形同値。 -/
def asSmallHomCochainEquiv (P Q : CochainComplex (J ⥤ ModuleCat.{u} A) ℤ) (n : ℤ) :
    Cochain P Q n ≃ₗ[A]
      Cochain ((asSmallComplexRestriction A J).obj P) ((asSmallComplexRestriction A J).obj Q) n where
  toFun z := z.map ((Functor.whiskeringLeft (AsSmall.{u} J) J (ModuleCat A)).obj AsSmall.down)
  invFun z := Cochain.mk (fun p q hpq => Functor.whiskerLeft (AsSmall.up : J ⥤ AsSmall.{u} J) (z.v p q hpq))
  left_inv z := by
    apply Cochain.ext
    intro p q hpq
    apply NatTrans.ext
    funext j
    rfl
  right_inv z := by
    apply Cochain.ext
    intro p q hpq
    apply NatTrans.ext
    funext j
    rfl
  map_add' z z' := Cochain.map_add _ _ _
  map_smul' r z := by
    apply Cochain.ext
    intro p q hpq
    apply NatTrans.ext
    funext j
    rfl
/-- 同じ添字制限による元の線形Hom複体の同型。 -/
def asSmallLinearHomIso (P Q : CochainComplex (J ⥤ ModuleCat.{u} A) ℤ) :
    linearHomComplex A P Q ≅
      linearHomComplex A ((asSmallComplexRestriction A J).obj P) ((asSmallComplexRestriction A J).obj Q) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (asSmallHomCochainEquiv A J P Q n).toModuleIso)
    (fun i j _ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact (δ_map i j z
        ((Functor.whiskeringLeft (AsSmall.{u} J) J (ModuleCat A)).obj AsSmall.down)).symm)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
