module

public import SerrePositivity.KST.Comparison.LocalCoefficientsOver

/-!
# 基底上の局所係数複体の関手

概要：固定した局所係数系に対し、基底上の単体集合から鎖複体への関手を構成する。
方針：基底との可換性による係数輸送の合成法則を、Kan 拡張の単位で照合する。
規約：Weibel K-book IV.1.6。正規化・非正規化の双方の複体を明示する。
使われ方：horn 添付の局所係数の余極限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory AlgebraicTopology

/--
概要：基底上の恒等射の局所係数の誘導写像は恒等射である。
方針：係数輸送と基底の写像のそれぞれの恒等法則を使う。
規約：単体的アーベル群の段階。
使われ方：基底上の関手の恒等法則。
-/
theorem overLocalCoefficientSimplicialMap_id {B : SSet.{u}} (L : LocalCoefficientSystem B)
    (X : Over B) : overLocalCoefficientSimplicialMap L (𝟙 X) =
      𝟙 ((coefficientSimplicialFunctor X.left).obj
        (pullbackLocalCoefficients X.hom L).coefficients) := by
  let F := coefficientSimplicialFunctor X.left
  let K := (pullbackLocalCoefficients X.hom L).coefficients
  have ha : F.map (overLocalCoefficientSourceIso L (𝟙 X)).hom = 𝟙 (F.obj K) :=
    (congrArg F.map (overLocalCoefficientSourceIso_id L X)).trans (F.map_id K)
  have hb : localCoefficientSimplicialMap (𝟙 X.left) (pullbackLocalCoefficients X.hom L) =
      𝟙 (F.obj K) := localCoefficientSimplicialMap_id _ _
  change F.map (overLocalCoefficientSourceIso L (𝟙 X)).hom ≫
    localCoefficientSimplicialMap (𝟙 X.left) (pullbackLocalCoefficients X.hom L) = _
  exact (congrArg₂ (fun a b => a ≫ b) ha hb).trans (Category.id_comp _)

/--
概要：基底上の局所係数の誘導写像は合成を保つ。
方針：Kan 拡張の単位で判定し、可換性からの係数輸送の合成法則を使う。
規約：固定した基底と固定した局所係数系。
使われ方：slice 圏の関手の合成法則。
-/
@[reassoc] theorem overLocalCoefficientSimplicialMap_comp {B : SSet.{u}}
    (L : LocalCoefficientSystem B) {X Y Z : Over B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    overLocalCoefficientSimplicialMap L f ≫ overLocalCoefficientSimplicialMap L g =
      overLocalCoefficientSimplicialMap L (f ≫ g) := by
  apply Functor.leftKanExtension_hom_ext (Functor.Elements.π X.left)
    (pullbackLocalCoefficients X.hom L).coefficients
  apply NatTrans.ext
  funext e
  let uX := ((Functor.Elements.π X.left).leftKanExtensionUnit
    (pullbackLocalCoefficients X.hom L).coefficients).app e
  let uY := ((Functor.Elements.π Y.left).leftKanExtensionUnit
    (pullbackLocalCoefficients Y.hom L).coefficients).app (f.left.mapElements.obj e)
  let uZ := ((Functor.Elements.π Z.left).leftKanExtensionUnit
    (pullbackLocalCoefficients Z.hom L).coefficients).app ((f ≫ g).left.mapElements.obj e)
  let a := (overLocalCoefficientSimplicialMap L f).app e.obj
  let b := (overLocalCoefficientSimplicialMap L g).app e.obj
  let c := (overLocalCoefficientSimplicialMap L (f ≫ g)).app e.obj
  let t := (overLocalCoefficientSourceIso L f).hom.app e
  let s := (overLocalCoefficientSourceIso L g).hom.app (f.left.mapElements.obj e)
  let v := (overLocalCoefficientSourceIso L (f ≫ g)).hom.app e
  have ha : uX ≫ a = t ≫ uY := overLocalCoefficientSimplicialMap_unit L f e
  have hb : uY ≫ b = s ≫ uZ :=
    overLocalCoefficientSimplicialMap_unit L g (f.left.mapElements.obj e)
  have hc : uX ≫ c = v ≫ uZ := overLocalCoefficientSimplicialMap_unit L (f ≫ g) e
  have ht : t ≫ s = v :=
    (congrArg (fun q => q.app e) (overLocalCoefficientSourceIso_comp L f g)).symm
  change uX ≫ (a ≫ b) = uX ≫ c
  calc
    _ = (uX ≫ a) ≫ b := (Category.assoc _ _ _).symm
    _ = (t ≫ uY) ≫ b := congrArg (fun q => q ≫ b) ha
    _ = t ≫ (s ≫ uZ) := by rw [Category.assoc, hb]
    _ = (t ≫ s) ≫ uZ := (Category.assoc _ _ _).symm
    _ = v ≫ uZ := congrArg (fun q => q ≫ uZ) ht
    _ = uX ≫ c := hc.symm

/--
概要：基底上の単体集合から引き戻し局所係数の単体的群への関手。
方針：構成した誘導写像と恒等・合成法則を束ねる。
規約：固定した基底の局所係数系を全ての対象で使う。
使われ方：係数群の直和による余極限の計算。
-/
def overLocalCoefficientSimplicialFunctor {B : SSet.{u}} (L : LocalCoefficientSystem B) :
    Over B ⥤ SimplicialObject AddCommGrpCat.{u} where
  obj X := (coefficientSimplicialFunctor X.left).obj
    (pullbackLocalCoefficients X.hom L).coefficients
  map f := overLocalCoefficientSimplicialMap L f
  map_id X := overLocalCoefficientSimplicialMap_id L X
  map_comp f g := (overLocalCoefficientSimplicialMap_comp L f g).symm

/--
概要：基底上の単体集合から局所係数の正規化鎖複体への関手。
方針：単体的アーベル群の関手に Moore 正規化を合成する。
規約：対象は固定した基底の局所係数の引き戻しを用いる。
使われ方：plus の局所係数の相対複体。
-/
def overLocalCoefficientChainsFunctor {B : SSet.{u}} (L : LocalCoefficientSystem B) :
    Over B ⥤ ChainComplex AddCommGrpCat.{u} ℕ :=
  overLocalCoefficientSimplicialFunctor L ⋙ normalizedMooreComplex _

/--
概要：基底上の単体集合から局所係数の非正規化鎖複体への関手。
方針：単体的アーベル群の関手に交互面複体を合成する。
規約：余極限の計算ではこちらの模型を使う。
使われ方：horn 添付の pushout と超限合成。
-/
def overLocalCoefficientUnnormalizedChainsFunctor {B : SSet.{u}} (L : LocalCoefficientSystem B) :
    Over B ⥤ ChainComplex AddCommGrpCat.{u} ℕ :=
  overLocalCoefficientSimplicialFunctor L ⋙ alternatingFaceMapComplex _

end SerrePositivity.KST.Comparison
