module

public import SerrePositivity.KST.Comparison.LocalCoefficientFibers
public import SerrePositivity.KST.Comparison.IntegerCoefficientGroup

/-!
# 定数整数係数と自由アーベル群模型の比較

概要：定数整数局所係数の単体的群を、整数鎖複体の自由アーベル群模型と比較する。
方針：各単体に生成元を送る射から Kan 拡張の普遍性で比較を作る。
規約：Weibel K-book IV.1.6。整数群は一点上の自由アーベル群として宇宙を保つ。
使われ方：局所係数のホモロジー同型から整数係数での帰結を導く。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

/--
概要：各単体に対応する自由群の生成元を指定する自然変換。
方針：一点からその単体への写像に自由アーベル群関手を適用する。
規約：整数定数係数から自由単体的アーベル群への元の圏上の射。
使われ方：Kan 拡張による整数比較写像。
-/
def integerCoefficientUnit (X : SSet.{u}) :
    (constantLocalCoefficients X integerCoefficientGroup).coefficients ⟶
      Functor.Elements.π X ⋙ freeAbelianSimplicialFunctor.obj X where
  app e := integerGeneratorMap e.val
  naturality {e e'} f := by
    change 𝟙 integerCoefficientGroup ≫ integerGeneratorMap e'.val =
      integerGeneratorMap e.val ≫ AddCommGrpCat.free.map (X.map f.hom)
    rw [Category.id_comp]
    dsimp only [integerGeneratorMap]
    rw [← AddCommGrpCat.free.map_comp]
    congr 1
    ext _
    exact f.map_val.symm

/--
概要：定数整数局所係数の単体的群から自由単体的アーベル群への自然変換。
方針：各単体の生成元を指定する自然変換を左 Kan 拡張する。
規約：単体次数での自然性を備える実際の比較写像。
使われ方：正規化複体とホモロジーの比較。
-/
def integerCoefficientComparison (X : SSet.{u}) :
    (coefficientSimplicialFunctor X).obj
      (constantLocalCoefficients X integerCoefficientGroup).coefficients ⟶
        freeAbelianSimplicialFunctor.obj X :=
  Functor.descOfIsLeftKanExtension _
    ((Functor.Elements.π X).leftKanExtensionUnit
      (constantLocalCoefficients X integerCoefficientGroup).coefficients) _
      (integerCoefficientUnit X)

/--
概要：整数係数の比較は各単体の生成元を対応する自由群の生成元へ送る。
方針：Kan 拡張の普遍性の因子分解式を使う。
規約：任意の元の圏の対象での式。
使われ方：直和表示を通しての比較写像の可逆性。
-/
@[reassoc] theorem integerCoefficientComparison_unit (X : SSet.{u}) (e : X.Elements) :
    ((Functor.Elements.π X).leftKanExtensionUnit
      (constantLocalCoefficients X integerCoefficientGroup).coefficients).app e ≫
        (integerCoefficientComparison X).app e.obj = integerGeneratorMap e.val :=
  Functor.descOfIsLeftKanExtension_fac_app _ _ _ _ e

/--
概要：定数整数係数の各次数の群と自由整数鎖群の同型。
方針：係数群の直和表示と、整数直和の自由アーベル群との同型を合成する。
規約：各次数の同型の自然性は比較写像との一致から導く。
使われ方：単体的整数比較の可逆性。
-/
def integerCoefficientObjIso (X : SSet.{u}) (d : SimplexCategoryᵒᵖ) :
    ((coefficientSimplicialFunctor X).obj
      (constantLocalCoefficients X integerCoefficientGroup).coefficients).obj d ≅
        (freeAbelianSimplicialFunctor.obj X).obj d :=
  coefficientSimplicialObjIsoSigma X
    (constantLocalCoefficients X integerCoefficientGroup).coefficients d ≪≫
      integerCoefficientCoproductIso (X.obj d)

/--
概要：Kan 拡張による整数比較は次数ごとの直和の同型と一致する。
方針：各単体の包含との合成を Kan 拡張の単位の式で照合する。
規約：比較写像の可逆性を仮定しない。
使われ方：実際の単体的同型を構成する。
-/
theorem integerCoefficientComparison_app (X : SSet.{u}) (d : SimplexCategoryᵒᵖ) :
    (integerCoefficientComparison X).app d = (integerCoefficientObjIso X d).hom := by
  let L := (constantLocalCoefficients X integerCoefficientGroup).coefficients
  let e := coefficientSimplicialObjIsoSigma X L d
  have h : e.inv ≫ (integerCoefficientComparison X).app d =
      (integerCoefficientCoproductIso (X.obj d)).hom := by
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
          (integerCoefficientComparison X).app d := by rw [← Category.assoc, hi]
      _ = integerGeneratorMap x := integerCoefficientComparison_unit X (X.elementsMk d x)
      _ = _ := (Sigma.ι_comp_desc (fun x => integerGeneratorMap x) x).symm
  apply (cancel_epi e.inv).mp
  change e.inv ≫ (integerCoefficientComparison X).app d =
    e.inv ≫ (e.hom ≫ (integerCoefficientCoproductIso (X.obj d)).hom)
  rw [h, Iso.inv_hom_id_assoc]

/--
概要：定数整数局所係数の単体的アーベル群は自由単体的アーベル群に同型である。
方針：生成元を送る自然変換の各成分が同型であることを使う。
規約：正規化する前の実際の自然同型。
使われ方：整数鎖複体と整数ホモロジーへの比較。
-/
def integerCoefficientSimplicialIso (X : SSet.{u}) :
    (coefficientSimplicialFunctor X).obj
      (constantLocalCoefficients X integerCoefficientGroup).coefficients ≅
        freeAbelianSimplicialFunctor.obj X := by
  haveI (d : SimplexCategoryᵒᵖ) : IsIso ((integerCoefficientComparison X).app d) := by
    rw [integerCoefficientComparison_app]
    infer_instance
  have : IsIso (integerCoefficientComparison X) := NatIso.isIso_of_isIso_app _
  exact asIso (integerCoefficientComparison X)

/--
概要：定数整数局所係数の正規化複体と整数鎖複体の同型。
方針：構成した単体的群の自然同型に Moore 正規化を施す。
規約：実際の複体の同型。
使われ方：局所係数ホモロジーから整数ホモロジーへの帰結。
-/
def integerLocalCoefficientChainsIso (X : SSet.{u}) :
    localCoefficientChains X (constantLocalCoefficients X integerCoefficientGroup) ≅
      normalizedIntegralChains.obj X :=
  (normalizedMooreComplex _).mapIso (integerCoefficientSimplicialIso X)

/--
概要：定数整数局所係数ホモロジーと正規化整数ホモロジーの同型。
方針：整数係数の鎖複体の比較同型にホモロジー関手を施す。
規約：全自然数次数。
使われ方：acyclic 性の整数係数での帰結。
-/
def integerLocalCoefficientHomologyIso (X : SSet.{u}) (n : ℕ) :
    localCoefficientHomology X (constantLocalCoefficients X integerCoefficientGroup) n ≅
      integralHomology X n :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (integerLocalCoefficientChainsIso X)

end SerrePositivity.KST.Comparison
