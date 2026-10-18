module

public import SerrePositivity.KST.Comparison.IntegerCoefficientNaturality

/-!
# 局所係数変換と基底の写像の自然性

概要：係数変換と単体写像による誘導鎖写像の可換性を証明する。
方針：左 Kan 拡張の単位の自然性で各単体の成分に帰着する。
規約：Weibel K-book IV.1.6。局所係数の自明化による比較を実際の誘導写像と接続する。
使われ方：標準単体上の局所係数の horn 計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory AlgebraicTopology

/--
概要：係数変換による左 Kan 拡張の写像は単位と可換である。
方針：左 Kan 拡張の関手の単位の自然性を各単体で評価する。
規約：任意の係数関手の自然変換。
使われ方：基底の写像との可換性。
-/
@[reassoc] theorem coefficientSimplicialFunctor_map_unit (X : SSet.{u})
    {L K : X.Elements ⥤ AddCommGrpCat.{u}} (η : L ⟶ K) (e : X.Elements) :
    ((Functor.Elements.π X).leftKanExtensionUnit L).app e ≫
      ((coefficientSimplicialFunctor X).map η).app e.obj =
    η.app e ≫ ((Functor.Elements.π X).leftKanExtensionUnit K).app e :=
  (congrArg (fun q => q.app e) ((Functor.Elements.π X).lanUnit.naturality η)).symm

/--
概要：係数変換と基底の単体写像の誘導写像は可換である。
方針：源の Kan 拡張の単位で判定し、二つの因子分解式を比較する。
規約：源の係数変換は基底の写像に沿って引き戻す。
使われ方：自明化に関する局所係数の自然性。
-/
theorem localCoefficientSimplicialMap_naturality {X Y : SSet.{u}} (f : X ⟶ Y)
    (L K : LocalCoefficientSystem Y) (η : L.coefficients ⟶ K.coefficients) :
    (coefficientSimplicialFunctor X).map (Functor.whiskerLeft f.mapElements η) ≫
      localCoefficientSimplicialMap f K =
    localCoefficientSimplicialMap f L ≫ (coefficientSimplicialFunctor Y).map η := by
  apply Functor.leftKanExtension_hom_ext (Functor.Elements.π X)
    (pullbackLocalCoefficients f L).coefficients
  apply NatTrans.ext
  funext e
  let uL := ((Functor.Elements.π X).leftKanExtensionUnit
    (pullbackLocalCoefficients f L).coefficients).app e
  let uK := ((Functor.Elements.π X).leftKanExtensionUnit
    (pullbackLocalCoefficients f K).coefficients).app e
  let vL := ((Functor.Elements.π Y).leftKanExtensionUnit L.coefficients).app (f.mapElements.obj e)
  let vK := ((Functor.Elements.π Y).leftKanExtensionUnit K.coefficients).app (f.mapElements.obj e)
  let a := ((coefficientSimplicialFunctor X).map (Functor.whiskerLeft f.mapElements η)).app e.obj
  let b := (localCoefficientSimplicialMap f K).app e.obj
  let c := (localCoefficientSimplicialMap f L).app e.obj
  let d := ((coefficientSimplicialFunctor Y).map η).app e.obj
  let t := η.app (f.mapElements.obj e)
  have ha : uL ≫ a = t ≫ uK := coefficientSimplicialFunctor_map_unit X _ e
  have hb : uK ≫ b = vK := localCoefficientSimplicialMap_unit f K e
  have hc : uL ≫ c = vL := localCoefficientSimplicialMap_unit f L e
  have hd : vL ≫ d = t ≫ vK := coefficientSimplicialFunctor_map_unit Y _ _
  change uL ≫ (a ≫ b) = uL ≫ (c ≫ d)
  calc
    _ = (uL ≫ a) ≫ b := (Category.assoc _ _ _).symm
    _ = (t ≫ uK) ≫ b := congrArg (fun q => q ≫ b) ha
    _ = t ≫ vK := by rw [Category.assoc, hb]
    _ = vL ≫ d := hd.symm
    _ = (uL ≫ c) ≫ d := congrArg (fun q => q ≫ d) hc.symm
    _ = uL ≫ (c ≫ d) := Category.assoc _ _ _

/--
概要：係数変換と基底の写像の正規化鎖写像は可換である。
方針：単体的アーベル群での自然性に Moore 正規化を施す。
規約：係数変換の実際の Kan 拡張を使う。
使われ方：係数の自明化からホモロジーへの移送。
-/
theorem localCoefficientChainsMap_naturality {X Y : SSet.{u}} (f : X ⟶ Y)
    (L K : LocalCoefficientSystem Y) (η : L.coefficients ⟶ K.coefficients) :
    (normalizedMooreComplex _).map
      ((coefficientSimplicialFunctor X).map (Functor.whiskerLeft f.mapElements η)) ≫
        localCoefficientChainsMap f K =
    localCoefficientChainsMap f L ≫
      (normalizedMooreComplex _).map ((coefficientSimplicialFunctor Y).map η) := by
  change (normalizedMooreComplex _).map _ ≫ (normalizedMooreComplex _).map _ =
    (normalizedMooreComplex _).map _ ≫ (normalizedMooreComplex _).map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    localCoefficientSimplicialMap_naturality]

end SerrePositivity.KST.Comparison
