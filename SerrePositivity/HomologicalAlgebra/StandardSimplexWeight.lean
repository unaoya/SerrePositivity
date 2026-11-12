module

public import SerrePositivity.HomologicalAlgebra.StandardSimplexCoefficientContraction
public import SerrePositivity.HomologicalAlgebra.AugmentedChainFunctorComparison
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import all SerrePositivity.HomologicalAlgebra.FreePresheafFunctor
import all SerrePositivity.HomologicalAlgebra.StandardSimplexCoefficientContraction

/-!
# 標準単体の線形重みの増大

## 概要
標準単体の Hom を添字とする自由係数の前層を、全単体次数で増大する。

## 方針
自由表現可能前層の全関手を使い、唯一の終対象への写像を係数の余積へ移す。

## 規約
重みの基底は (Δᵒᵖ)ᵒᵖ とし、二重 opposite を暗黙の等号で消さない。

## 使われ方
Weibel §2.2、HA 1.2.4。bar 重みと標準単体の重みの射影分解による比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C]

/-- 各次数が自由表現可能前層である、標準単体の係数付き重み。 -/
def standardSimplexWeight (P : C) : SimplicialObject (SimplexCategoryᵒᵖᵒᵖ ⥤ C) :=
  freePresheafFunctor SimplexCategoryᵒᵖ P

/-- 標準単体の増大の係数対象。終対象の同じ元で添字づけた P の余積を保つ。 -/
def standardSimplexWeightPoint (P : C) : SimplexCategoryᵒᵖᵒᵖ ⥤ C :=
  (Functor.const SimplexCategoryᵒᵖᵒᵖ).obj ((copowerFunctor P).obj (terminal (Type 0)))

/-- 各標準単体の元を終対象の唯一の元へ送る、全単体に自然な増大。 -/
def standardSimplexWeightAugmentation (P : C) :
    standardSimplexWeight P ⟶ (SimplicialObject.const _).obj (standardSimplexWeightPoint P) where
  app n :=
    { app k := (copowerFunctor P).map (terminal.from _)
      naturality {k l} r := by
        change (copowerFunctor P).map _ ≫ (copowerFunctor P).map _ =
          (copowerFunctor P).map _ ≫ 𝟙 _
        rw [Category.comp_id, ← (copowerFunctor P).map_comp]
        congr 1
        exact terminal.hom_ext _ _ }
  naturality {n m} r := by
    apply NatTrans.ext
    funext k
    change (copowerFunctor P).map _ ≫ (copowerFunctor P).map _ =
      (copowerFunctor P).map _ ≫ 𝟙 _
    rw [Category.comp_id, ← (copowerFunctor P).map_comp]
    congr 1
    exact terminal.hom_ext _ _

/-- 同じ増大と全単体作用を持つ、標準単体の係数付き増大重み。 -/
def standardSimplexWeightAugmented (P : C) :
    SimplicialObject.Augmented (SimplexCategoryᵒᵖᵒᵖ ⥤ C) where
  left := standardSimplexWeight P
  right := standardSimplexWeightPoint P
  hom := standardSimplexWeightAugmentation P

/-- ある標準単体での評価は、同じ Hom を添字とする係数付き増大単体。 -/
def standardSimplexWeightEvaluationIso (P : C) (k : SimplexCategory) :
    ((SimplicialObject.Augmented.whiskering (SimplexCategoryᵒᵖᵒᵖ ⥤ C) C).obj
      ((evaluation SimplexCategoryᵒᵖᵒᵖ C).obj (op (op k)))).obj
        (standardSimplexWeightAugmented P) ≅ standardCoefficientAugmented P k := by
  let Y := ((SimplicialObject.Augmented.whiskering (SimplexCategoryᵒᵖᵒᵖ ⥤ C) C).obj
    ((evaluation SimplexCategoryᵒᵖᵒᵖ C).obj (op (op k)))).obj
      (standardSimplexWeightAugmented P)
  let E (n : SimplexCategoryᵒᵖ) : ((op k) ⟶ n) ≅ (n.unop ⟶ k) :=
    Equiv.toIso
      { toFun := Quiver.Hom.unop
        invFun := Quiver.Hom.op
        left_inv := Quiver.Hom.op_unop
        right_inv := Quiver.Hom.unop_op }
  let e : Y.left ≅ (standardCoefficientAugmented P k).left :=
    NatIso.ofComponents (fun n => (copowerFunctor P).mapIso (E n)) (by
      intro n m r
      change (copowerFunctor P).map _ ≫ (copowerFunctor P).map _ =
        (copowerFunctor P).map _ ≫ (copowerFunctor P).map _
      rw [← (copowerFunctor P).map_comp, ← (copowerFunctor P).map_comp]
      congr 1)
  exact Comma.isoMk e (Iso.refl _) (by
    apply NatTrans.ext
    funext n
    dsimp [e, Y, standardCoefficientAugmented, rawSimplexAugmented,
      standardSimplexWeightAugmented, standardSimplexWeightAugmentation,
      SimplicialObject.Augmented.whiskering, SimplicialObject.Augmented.whiskeringObj]
    have hc : (E n).hom ≫ terminal.from (n.unop ⟶ k) =
        terminal.from ((op k) ⟶ n) := terminal.hom_ext _ _
    have hf : (copowerFunctor P).map (E n).hom ≫
        (copowerFunctor P).map (terminal.from (n.unop ⟶ k)) =
        (copowerFunctor P).map (terminal.from ((op k) ⟶ n)) :=
      ((copowerFunctor P).map_comp _ _).symm.trans (congrArg (copowerFunctor P).map hc)
    simp only [CategoryTheory.Functor.constComp] 
    change (copowerFunctor P).map (E n).hom ≫
      ((copowerFunctor P).map (terminal.from (n.unop ⟶ k)) ≫ 𝟙 _) =
      ((copowerFunctor P).map (terminal.from ((op k) ⟶ n)) ≫ 𝟙 _) ≫ 𝟙 _
    rw [Category.comp_id, Category.comp_id, Category.comp_id]
    exact hf)

/-- 射影係数のとき、標準単体の重みの交代面複体は各次数で射影的。 -/
theorem standardSimplexWeight_projective [Preadditive C] [HasPushouts C] (P : C) [Projective P] (n : ℕ) :
    Projective ((AlternatingFaceMapComplex.obj (standardSimplexWeight P)).X n) :=
  freePresheafFunctor_projective SimplexCategoryᵒᵖ P (op (SimplexCategory.mk n))

/-- 同じ標準重みの増大鎖写像は、各評価の指定収縮によって擬同型。 -/
theorem standardSimplexWeight_augmentation_quasiIso [Abelian C] (P : C) :
    QuasiIso (AlternatingFaceMapComplex.ε.app (standardSimplexWeightAugmented P)) := by
  apply augmentedChain_quasiIso_of_evaluationExtraDegeneracy
  intro k
  exact SimplicialObject.Augmented.ExtraDegeneracy.ofIso
    (standardSimplexWeightEvaluationIso P k.unop.unop).symm
    (standardCoefficientExtraDegeneracy P k.unop.unop)

/-- 標準単体の線形重みは、同じ増大を持つ定数係数前層の射影分解。 -/
def standardSimplexWeightResolution [Abelian C] (P : C) [Projective P] :
    ProjectiveResolution (standardSimplexWeightPoint P) where
  complex := AlternatingFaceMapComplex.obj (standardSimplexWeight P)
  projective n := standardSimplexWeight_projective P n
  π := AlternatingFaceMapComplex.ε.app (standardSimplexWeightAugmented P)
  quasiIso := standardSimplexWeight_augmentation_quasiIso P

end SerrePositivity.HomologicalAlgebra
