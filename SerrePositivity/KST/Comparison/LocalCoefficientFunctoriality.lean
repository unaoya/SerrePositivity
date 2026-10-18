module

public import SerrePositivity.KST.Comparison.LocalCoefficientNaturality

/-!
# 局所係数の誘導写像の関手性

概要：引き戻し局所係数による実際の誘導写像が恒等射と合成を保つことを証明する。
方針：左 Kan 拡張の単位による因子分解式で判定する。
規約：Weibel K-book IV.1.6。係数の引き戻しの合成と整合させる。
使われ方：基底上の単体集合の圏から局所係数複体への関手。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory AlgebraicTopology

/--
概要：恒等写像の局所係数の単体的誘導写像は恒等射である。
方針：左 Kan 拡張の単位で判定する。
規約：恒等写像による引き戻し係数は元の係数と一致する。
使われ方：局所係数鎖複体の関手性。
-/
theorem localCoefficientSimplicialMap_id (X : SSet.{u}) (L : LocalCoefficientSystem X) :
    localCoefficientSimplicialMap (𝟙 X) L =
      𝟙 ((coefficientSimplicialFunctor X).obj L.coefficients) := by
  apply Functor.leftKanExtension_hom_ext (Functor.Elements.π X) L.coefficients
  apply NatTrans.ext
  funext e
  let u := ((Functor.Elements.π X).leftKanExtensionUnit L.coefficients).app e
  have hu : u ≫ (localCoefficientSimplicialMap (𝟙 X) L).app e.obj = u :=
    localCoefficientSimplicialMap_unit (𝟙 X) L e
  change u ≫ (localCoefficientSimplicialMap (𝟙 X) L).app e.obj = u ≫ 𝟙 _
  exact hu.trans (Category.comp_id u).symm

/--
概要：局所係数の単体的誘導写像は基底の写像の合成を保つ。
方針：三つの Kan 拡張の単位を比較し、普遍性の一意性を使う。
規約：最初の写像の係数は後の写像に沿って引き戻す。
使われ方：局所係数の鎖写像の合成。
-/
@[reassoc] theorem localCoefficientSimplicialMap_comp {X Y Z : SSet.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (L : LocalCoefficientSystem Z) :
    localCoefficientSimplicialMap f (pullbackLocalCoefficients g L) ≫
      localCoefficientSimplicialMap g L = localCoefficientSimplicialMap (f ≫ g) L := by
  apply Functor.leftKanExtension_hom_ext (Functor.Elements.π X)
    (pullbackLocalCoefficients (f ≫ g) L).coefficients
  apply NatTrans.ext
  funext e
  let uX := ((Functor.Elements.π X).leftKanExtensionUnit
    (pullbackLocalCoefficients (f ≫ g) L).coefficients).app e
  let uY := ((Functor.Elements.π Y).leftKanExtensionUnit
    (pullbackLocalCoefficients g L).coefficients).app (f.mapElements.obj e)
  let uZ := ((Functor.Elements.π Z).leftKanExtensionUnit L.coefficients).app
    ((f ≫ g).mapElements.obj e)
  let a := (localCoefficientSimplicialMap f (pullbackLocalCoefficients g L)).app e.obj
  let b := (localCoefficientSimplicialMap g L).app e.obj
  let c := (localCoefficientSimplicialMap (f ≫ g) L).app e.obj
  have ha : uX ≫ a = uY := localCoefficientSimplicialMap_unit f _ e
  have hb : uY ≫ b = uZ := localCoefficientSimplicialMap_unit g L (f.mapElements.obj e)
  have hc : uX ≫ c = uZ := localCoefficientSimplicialMap_unit (f ≫ g) L e
  change uX ≫ (a ≫ b) = uX ≫ c
  calc
    _ = (uX ≫ a) ≫ b := (Category.assoc _ _ _).symm
    _ = uY ≫ b := congrArg (fun q => q ≫ b) ha
    _ = uZ := hb
    _ = uX ≫ c := hc.symm

/--
概要：恒等写像の局所係数の正規化鎖写像は恒等射である。
方針：単体的写像の恒等法則に正規化関手を適用する。
規約：実際の局所係数鎖複体。
使われ方：局所係数複体の関手の恒等法則。
-/
theorem localCoefficientChainsMap_id (X : SSet.{u}) (L : LocalCoefficientSystem X) :
    localCoefficientChainsMap (𝟙 X) L = 𝟙 (localCoefficientChains X L) := by
  change (normalizedMooreComplex _).map (localCoefficientSimplicialMap (𝟙 X) L) = _
  exact (congrArg (fun q => (normalizedMooreComplex AddCommGrpCat.{u}).map q)
    (localCoefficientSimplicialMap_id X L)).trans
      ((normalizedMooreComplex AddCommGrpCat.{u}).map_id _)

/--
概要：局所係数の正規化鎖写像は基底の写像の合成を保つ。
方針：単体的誘導写像の合成法則に正規化関手を適用する。
規約：最初の係数系は後の写像に沿った引き戻し。
使われ方：基底上の局所係数複体の関手性。
-/
@[reassoc] theorem localCoefficientChainsMap_comp {X Y Z : SSet.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (L : LocalCoefficientSystem Z) :
    localCoefficientChainsMap f (pullbackLocalCoefficients g L) ≫
      localCoefficientChainsMap g L = localCoefficientChainsMap (f ≫ g) L := by
  change (normalizedMooreComplex _).map _ ≫ (normalizedMooreComplex _).map _ =
    (normalizedMooreComplex _).map _
  rw [← CategoryTheory.Functor.map_comp, localCoefficientSimplicialMap_comp]

end SerrePositivity.KST.Comparison
