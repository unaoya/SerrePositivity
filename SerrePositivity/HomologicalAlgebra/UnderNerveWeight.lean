module

public import SerrePositivity.HomologicalAlgebra.InitialNerveExtraDegeneracy
public import SerrePositivity.HomologicalAlgebra.FreePresheafFunctor
public import SerrePositivity.HomologicalAlgebra.AugmentedChainFunctorComparison
public import Mathlib.CategoryTheory.Comma.Over.Basic
import all SerrePositivity.HomologicalAlgebra.FreePresheafFunctor
import all SerrePositivity.HomologicalAlgebra.InitialNerveExtraDegeneracy

/-!
# under 圏の nerve による係数付き bar 重み

## 概要
各対象 x に under 圏 x/J の nerve を割り当て、その各単体で係数 P の余積を取る。

## 方針
元の under の前合成と nerve の全関手を使い、増大の各評価を始対象で収縮する。

## 規約
重みは Jᵒᵖ 上の前層。先頭の係数を使う bar と同じ向きを保つ。

## 使われ方
Weibel §2.2、HA 1.2.4。標準単体の線形重みと比較する bar の射影分解。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
namespace SerrePositivity.HomologicalAlgebra
variable (J : Type) [SmallCategory J]
variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C]

/-- x/J の元の全射列を値とする、反変な集合的 bar 重み。 -/
def underNerveWeight : Jᵒᵖ ⥤ SSet.{0} := Under.mapFunctor J ⋙ nerveFunctor

/-- 同じ under nerve の各単体で P の余積を取った、係数付き bar 重み。 -/
def coefficientBarWeight (P : C) : SimplicialObject (Jᵒᵖ ⥤ C) :=
  (underNerveWeight J ⋙
    (SimplicialObject.whiskering (Type 0) C).obj (copowerFunctor P)).flip

/-- 同じ under 射列の P の直和因子の標準包含。 -/
def coefficientBarWeightι (P : C) (n : SimplexCategoryᵒᵖ) (x : Jᵒᵖ)
    (τ : ComposableArrows (Under x.unop) n.unop.len) :
    P ⟶ ((coefficientBarWeight J P).obj n).obj x :=
  Sigma.ι (fun _ : ComposableArrows (Under x.unop) n.unop.len => P) τ

/-- 底の前合成は、同じ射列の標準包含を前合成した射列の標準包含へ送る。 -/
@[reassoc (attr := simp)]
theorem coefficientBarWeightι_map (P : C) (n : SimplexCategoryᵒᵖ)
    {x y : Jᵒᵖ} (f : x ⟶ y) (τ : ComposableArrows (Under x.unop) n.unop.len) :
    coefficientBarWeightι J P n x τ ≫ ((coefficientBarWeight J P).obj n).map f =
      coefficientBarWeightι J P n y (τ ⋙ Under.map f.unop) := by
  simp [coefficientBarWeightι, coefficientBarWeight, underNerveWeight, copowerFunctor]
  rfl

/-- bar の同じ増大の係数対象。 -/
def coefficientBarWeightPoint (P : C) : Jᵒᵖ ⥤ C :=
  (Functor.const Jᵒᵖ).obj ((copowerFunctor P).obj (terminal (Type 0)))

/-- 全単体と全対象に自然な、同じ bar 重みの増大。 -/
def coefficientBarWeightAugmentation (P : C) : coefficientBarWeight J P ⟶
    (SimplicialObject.const _).obj (coefficientBarWeightPoint J P) where
  app n :=
    { app x := (copowerFunctor P).map (terminal.from _)
      naturality {x y} f := by
        change (copowerFunctor P).map _ ≫ (copowerFunctor P).map _ =
          (copowerFunctor P).map _ ≫ 𝟙 _
        rw [Category.comp_id, ← (copowerFunctor P).map_comp]
        congr 1
        exact terminal.hom_ext _ _ }
  naturality {n m} r := by
    apply NatTrans.ext
    funext x
    change (copowerFunctor P).map _ ≫ (copowerFunctor P).map _ =
      (copowerFunctor P).map _ ≫ 𝟙 _
    rw [Category.comp_id, ← (copowerFunctor P).map_comp]
    congr 1
    exact terminal.hom_ext _ _

/-- 元の同じ全単体作用・同じ係数を持つ、増大 bar 重み。 -/
def coefficientBarWeightAugmented (P : C) : SimplicialObject.Augmented (Jᵒᵖ ⥤ C) where
  left := coefficientBarWeight J P
  right := coefficientBarWeightPoint J P
  hom := coefficientBarWeightAugmentation J P

/-- bar 重みの各評価は、元の under 圏の同じ係数付き増大 nerve。 -/
def coefficientBarWeightEvaluationIso (P : C) (x : Jᵒᵖ) :
    ((SimplicialObject.Augmented.whiskering (Jᵒᵖ ⥤ C) C).obj
      ((evaluation Jᵒᵖ C).obj x)).obj (coefficientBarWeightAugmented J P) ≅
    ((SimplicialObject.Augmented.whiskering (Type 0) C).obj (copowerFunctor P)).obj
      (nerveAugmented (Under x.unop)) := by
  let Y := ((SimplicialObject.Augmented.whiskering (Jᵒᵖ ⥤ C) C).obj
    ((evaluation Jᵒᵖ C).obj x)).obj (coefficientBarWeightAugmented J P)
  let Z := ((SimplicialObject.Augmented.whiskering (Type 0) C).obj (copowerFunctor P)).obj
    (nerveAugmented (Under x.unop))
  let e : Y.left ≅ Z.left := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intros
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl)
  exact Comma.isoMk e (Iso.refl _) (by
    apply NatTrans.ext
    funext n
    simp [Y, Z, e, coefficientBarWeightAugmented, coefficientBarWeightAugmentation,
      nerveAugmented, underNerveWeight, SimplicialObject.Augmented.whiskering,
      SimplicialObject.Augmented.whiskeringObj, CategoryTheory.Functor.constComp]
    rfl)

/-- bar 重みの増大は、各 under 圏の恒等射の始対象によって擬同型となる。 -/
theorem coefficientBarWeight_augmentation_quasiIso [Abelian C] (P : C) :
    QuasiIso (AlternatingFaceMapComplex.ε.app (coefficientBarWeightAugmented J P)) := by
  apply augmentedChain_quasiIso_of_evaluationExtraDegeneracy
  intro x
  exact SimplicialObject.Augmented.ExtraDegeneracy.ofIso
    (coefficientBarWeightEvaluationIso J P x).symm
    ((initialNerveExtraDegeneracy (Under.mk (𝟙 x.unop)) Under.mkIdInitial).map
      (copowerFunctor P))

end SerrePositivity.HomologicalAlgebra
