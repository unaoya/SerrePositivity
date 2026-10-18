module

public import SerrePositivity.KST.Comparison.LocalCoefficientTrivialization
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# 定数局所係数と各次数の直和の比較

概要：任意のアーベル群の定数局所係数を、単体ごとの係数群の直和の模型へ移す。
方針：Kan 拡張の単位と直和包含を比較する。
規約：Weibel K-book IV.1.6。整数係数に限定しない。
使われ方：horn の局所係数計算の定数係数への帰着。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

/--
概要：単体集合の各次数で係数群の直和を取る関手。
方針：Mathlib の sigmaConst を単体次数ごとに適用する。
規約：任意のアーベル群係数。
使われ方：定数局所係数の交互面複体。
-/
def constantCoefficientSimplicialFunctor (G : AddCommGrpCat.{u}) :
    SSet.{u} ⥤ SimplicialObject AddCommGrpCat.{u} :=
  (Functor.whiskeringRight _ _ _).obj (sigmaConst.obj G)

/--
概要：各単体の係数群から直和のその単体の成分への包含。
方針：元の圏上で直和の包含を束ねる。
規約：定数係数系から直和模型への自然変換。
使われ方：左 Kan 拡張の普遍性。
-/
def constantCoefficientUnit (X : SSet.{u}) (G : AddCommGrpCat.{u}) :
    (constantLocalCoefficients X G).coefficients ⟶
      Functor.Elements.π X ⋙ (constantCoefficientSimplicialFunctor G).obj X where
  app e := Sigma.ι (fun _ : X.obj e.obj => G) e.val
  naturality {e e'} f := by
    change 𝟙 G ≫ Sigma.ι (fun _ : X.obj e'.obj => G) e'.val =
      Sigma.ι (fun _ : X.obj e.obj => G) e.val ≫
        Sigma.map' (X.map f.hom) (fun _ => 𝟙 G)
    simp only [Category.id_comp, Sigma.ι_comp_map']
    rw [f.map_val]

/--
概要：定数局所係数の単体的群から直和模型への比較写像。
方針：各単体の直和包含を左 Kan 拡張する。
規約：全ての面・退化と可換な自然変換。
使われ方：定数係数の複体の同型。
-/
def constantCoefficientComparison (X : SSet.{u}) (G : AddCommGrpCat.{u}) :
    (coefficientSimplicialFunctor X).obj (constantLocalCoefficients X G).coefficients ⟶
      (constantCoefficientSimplicialFunctor G).obj X :=
  Functor.descOfIsLeftKanExtension _
    ((Functor.Elements.π X).leftKanExtensionUnit (constantLocalCoefficients X G).coefficients)
    _ (constantCoefficientUnit X G)

/--
概要：定数係数の比較は Kan 拡張の単位を直和包含へ送る。
方針：左 Kan 拡張の因子分解式を評価する。
規約：任意の単体に対する式。
使われ方：比較写像の可逆性。
-/
@[reassoc] theorem constantCoefficientComparison_unit (X : SSet.{u}) (G : AddCommGrpCat.{u})
    (e : X.Elements) :
    ((Functor.Elements.π X).leftKanExtensionUnit
      (constantLocalCoefficients X G).coefficients).app e ≫
      (constantCoefficientComparison X G).app e.obj = Sigma.ι (fun _ : X.obj e.obj => G) e.val :=
  Functor.descOfIsLeftKanExtension_fac_app _ _ _ _ e

/--
概要：定数係数の比較は点ごとの Kan 拡張の直和同型と一致する。
方針：直和の全ての包含との合成を比較する。
規約：比較写像の可逆性を仮定しない。
使われ方：定数係数の実際の単体的同型。
-/
theorem constantCoefficientComparison_app (X : SSet.{u}) (G : AddCommGrpCat.{u})
    (d : SimplexCategoryᵒᵖ) :
    (constantCoefficientComparison X G).app d =
      (coefficientSimplicialObjIsoSigma X (constantLocalCoefficients X G).coefficients d).hom := by
  let L := (constantLocalCoefficients X G).coefficients
  let e := coefficientSimplicialObjIsoSigma X L d
  have h : e.inv ≫ (constantCoefficientComparison X G).app d = 𝟙 (∐ fun _ : X.obj d => G) := by
    apply Sigma.hom_ext
    intro x
    have hu := coefficientSimplicialObjIsoSigma_unit X L d x
    have hi : Sigma.ι (coefficientFiberFamily X L d) x ≫ e.inv =
        ((Functor.Elements.π X).leftKanExtensionUnit L).app (X.elementsMk d x) := by
      calc
        _ = (((Functor.Elements.π X).leftKanExtensionUnit L).app (X.elementsMk d x) ≫
            e.hom) ≫ e.inv := congrArg (fun q => q ≫ e.inv) hu.symm
        _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    calc
      _ = ((Functor.Elements.π X).leftKanExtensionUnit L).app (X.elementsMk d x) ≫
          (constantCoefficientComparison X G).app d := by rw [← Category.assoc, hi]
      _ = Sigma.ι (fun _ : X.obj d => G) x := constantCoefficientComparison_unit X G _
      _ = _ := (Category.comp_id _).symm
  apply (cancel_epi e.inv).mp
  exact h.trans e.inv_hom_id.symm

/--
概要：定数局所係数の単体的群は係数群の次数ごとの直和の模型と同型である。
方針：各成分の直和同型と一致する自然変換を同型にまとめる。
規約：任意のアーベル群係数。
使われ方：定数係数のホモトピー不変性を局所係数の定義へ移す。
-/
def constantCoefficientSimplicialIso (X : SSet.{u}) (G : AddCommGrpCat.{u}) :
    (coefficientSimplicialFunctor X).obj (constantLocalCoefficients X G).coefficients ≅
      (constantCoefficientSimplicialFunctor G).obj X := by
  have (d : SimplexCategoryᵒᵖ) : IsIso ((constantCoefficientComparison X G).app d) := by
    rw [constantCoefficientComparison_app]
    infer_instance
  have : IsIso (constantCoefficientComparison X G) := NatIso.isIso_of_isIso_app _
  exact asIso (constantCoefficientComparison X G)

end SerrePositivity.KST.Comparison
