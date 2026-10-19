module
public import SerrePositivity.InfinityCategories.Derived.ComplexPinchedModel

/-! # 実 pinched Hom と複体の単位 Hom 模型の比較

概要：任意 dg 圏の固定 Hom の実 pinched 空間を、複体模型へ自然に移す。
方針：単位 Hom の全次数鎖同型を実 pinched 空間へ送り、関手則で自然性を照合する。
規約：実際の単体的同型。使われ方：一般準同型の全射性仮定の除去。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded CochainComplex
variable {A : Type u} [CommRing A] {D E : Type v} [DGCategory A D] [DGCategory A E]

/-- 固定 Hom の実 pinched 空間と、その複体の単位 Hom 模型の実同型。 -/
def pinchedComplexModelIso (x y : D) :
    DGNerve.pinchedHom A D x y ≅ complexPinchedSpace.{u, v} (homObject A D x y) := by
  let f := pinchedHomChainMap
    (D := D) (E := DGComplexPinchedModel.{u, v} (homObject A D x y))
    (x := x) (y := y) (x' := complexPinchedSource _) (y' := complexPinchedTarget _)
    (complexUnitHomIso (homObject A D x y)).hom
  let : IsIso f := pinchedHomChainMap_isIso
    (D := D) (E := DGComplexPinchedModel.{u, v} (homObject A D x y))
    (x := x) (y := y) (x' := complexPinchedSource _) (y' := complexPinchedTarget _) _
  exact asIso f

/-- 単位 Hom 模型への比較は任意の Hom 鎖写像に関して厳密に自然。 -/
lemma pinchedComplexModelIso_naturality {x y : D} {x' y' : E}
    (φ : homObject A D x y ⟶ homObject A E x' y') :
    pinchedHomChainMap φ ≫ (pinchedComplexModelIso x' y').hom =
      (pinchedComplexModelIso x y).hom ≫ complexPinchedMap.{u, v} φ := by
  have h₁ := pinchedHomChainMap_comp
    (D := D) (E := E) (T := DGComplexPinchedModel.{u, v} (homObject A E x' y'))
    (x := x) (y := y) (x' := x') (y' := y')
    (x'' := complexPinchedSource _) (y'' := complexPinchedTarget _)
    φ (complexUnitHomIso (homObject A E x' y')).hom
  have h₂ := pinchedHomChainMap_comp
    (D := D) (E := DGComplexPinchedModel.{u, v} (homObject A D x y))
    (T := DGComplexPinchedModel.{u, v} (homObject A E x' y'))
    (x := x) (y := y) (x' := complexPinchedSource _) (y' := complexPinchedTarget _)
    (x'' := complexPinchedSource _) (y'' := complexPinchedTarget _)
    (complexUnitHomIso (homObject A D x y)).hom (homPostcompose (𝟙_ (Complex A)) φ)
  exact h₁.symm.trans ((congrArg (fun q => pinchedHomChainMap
    (D := D) (E := DGComplexPinchedModel.{u, v} (homObject A E x' y'))
    (x := x) (y := y) (x' := complexPinchedSource _) (y' := complexPinchedTarget _) q)
    (complexUnitHomIso_naturality φ).symm).trans h₂)

end SerrePositivity.InfinityCategories
