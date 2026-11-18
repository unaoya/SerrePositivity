module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConvolutionConstantNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConvolutionLimits

/-!
概要：元の底射を固定した相対乗法的写像の単体集合。
方針：実余単位からの定数単体を固定し、元の射の実 pullback を取る。
規約：全単体次数で元の底射を保つ。導来比較・Kan 性は未主張。
使われ方：Postnikov 拡大の固定底に相対的な導来比較の前段。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
open scoped Simplicial
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

abbrev simplexComonoid (n : SimplexCategory) :=
  (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexCochainComonFunctor R).obj n

def multiplicativeMappingBasePoint {A B : Mon (Complex R)} (s : A ⟶ B) :
    (multiplicativeMappingSimplices R A B) _⦋0⦌ :=
  s ≫ convolutionConstantMap R (simplexComonoid R ⦋0⦌) B

set_option maxHeartbeats 800000 in -- 実 AW 畳み込みと coyoneda の複合を全次数で同定する。
def multiplicativeMappingBase {A B : Mon (Complex R)} (s : A ⟶ B) :
    (Δ[0] : SSet.{u}) ⟶ multiplicativeMappingSimplices R A B :=
  { app := fun n => TypeCat.ofHom (fun _ =>
      s ≫ convolutionConstantMap R (simplexComonoid R n.unop) B)
    naturality := by
      intro m n f
      apply ConcreteCategory.hom_ext
      intro z
      change s ≫ convolutionConstantMap R (simplexComonoid R n.unop) B =
        (s ≫ convolutionConstantMap R (simplexComonoid R m.unop) B) ≫
          convolutionPrecompose R
            ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexCochainComonFunctor R).map f.unop) B
      rw [Category.assoc, convolutionConstantMap_precompose] }

lemma multiplicativeMappingBase_app {A B : Mon (Complex R)} (s : A ⟶ B)
    (n : SimplexCategoryᵒᵖ) (z : (Δ[0] : SSet.{u}).obj n) :
    (multiplicativeMappingBase R s).app n z =
      s ≫ convolutionConstantMap R (simplexComonoid R n.unop) B := rfl

variable {A X B : Mon (Complex R)} (q : X ⟶ B) (s : A ⟶ B)

def relativeMultiplicativeMappingSimplices : SSet.{u} :=
  pullback (multiplicativeMappingPostcompose R A q) (multiplicativeMappingBase R s)

def relativeMultiplicativeMappingProjection :
    relativeMultiplicativeMappingSimplices R q s ⟶ multiplicativeMappingSimplices R A X :=
  pullback.fst _ _

def relativeMultiplicativeMappingBaseProjection :
    relativeMultiplicativeMappingSimplices R q s ⟶ (Δ[0] : SSet.{u}) :=
  pullback.snd _ _

lemma relativeMultiplicativeMapping_condition :
    relativeMultiplicativeMappingProjection R q s ≫ multiplicativeMappingPostcompose R A q =
      relativeMultiplicativeMappingBaseProjection R q s ≫ multiplicativeMappingBase R s :=
  pullback.condition

lemma relativeMultiplicativeMapping_condition_app (n : SimplexCategoryᵒᵖ)
    (z : (relativeMultiplicativeMappingSimplices R q s).obj n) :
    (relativeMultiplicativeMappingProjection R q s).app n z ≫
        (convolutionFunctor R (simplexComonoid R n.unop)).map q =
      s ≫ convolutionConstantMap R (simplexComonoid R n.unop) B := by
  have h := ConcreteCategory.congr_hom
    (congr_app (relativeMultiplicativeMapping_condition R q s) n) z
  exact h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
