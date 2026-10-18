module

public import SerrePositivity.KST.Comparison.LocalCoefficientFunctoriality
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# 基底上の単体集合と局所係数の誘導写像

概要：固定した基底の局所係数を、その基底上の単体集合へ引き戻して比較する。
方針：基底との可換性から係数の同型を作り、Kan 拡張の係数変換と誘導写像を合成する。
規約：Weibel K-book IV.1.6。基底との可換性に由来する輸送を明示する。
使われ方：slice 圏での horn 添付と余極限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory AlgebraicTopology

/--
概要：基底上の射の可換性は引き戻し係数の自然同型を与える。
方針：基底への二つの合成の等式を係数の前合成へ渡す。
規約：元の係数の輸送を選び直さない。
使われ方：基底上の局所係数の誘導写像。
-/
def overLocalCoefficientSourceIso {B : SSet.{u}} (L : LocalCoefficientSystem B)
    {X Y : Over B} (f : X ⟶ Y) :
    (pullbackLocalCoefficients X.hom L).coefficients ≅
      f.left.mapElements ⋙ (pullbackLocalCoefficients Y.hom L).coefficients :=
  eqToIso (congrArg (fun p : X.left ⟶ B => (pullbackLocalCoefficients p L).coefficients) f.w.symm)

/--
概要：前合成は関手の等式からの標準射を保つ。
方針：等式を帰納して恒等射の場合へ帰着する。
規約：任意の三つの圏。
使われ方：基底との可換性による係数の輸送の合成。
-/
theorem coefficientWhiskerLeft_eqToHom {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) {G H : D ⥤ E} (h : G = H) :
    Functor.whiskerLeft F (eqToHom h) = eqToHom (congrArg (fun K => F ⋙ K) h) := by
  subst h
  rfl

/--
概要：恒等射に由来する引き戻し係数の輸送は恒等射である。
方針：等しい関手の標準射の定義を使う。
規約：基底上の恒等射。
使われ方：局所係数の基底上の関手の恒等法則。
-/
theorem overLocalCoefficientSourceIso_id {B : SSet.{u}} (L : LocalCoefficientSystem B)
    (X : Over B) : (overLocalCoefficientSourceIso L (𝟙 X)).hom =
      𝟙 (pullbackLocalCoefficients X.hom L).coefficients := rfl

/--
概要：基底上の二つの射の係数の輸送は合成と整合する。
方針：前合成が等式の標準射を保つことと標準射の合成法則を使う。
規約：右辺では二つ目の輸送を最初の射で引き戻す。
使われ方：基底上の誘導写像の合成法則。
-/
theorem overLocalCoefficientSourceIso_comp {B : SSet.{u}} (L : LocalCoefficientSystem B)
    {X Y Z : Over B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (overLocalCoefficientSourceIso L (f ≫ g)).hom =
      (overLocalCoefficientSourceIso L f).hom ≫
        Functor.whiskerLeft f.left.mapElements (overLocalCoefficientSourceIso L g).hom := by
  dsimp only [overLocalCoefficientSourceIso, eqToIso.hom]
  rw [coefficientWhiskerLeft_eqToHom, eqToHom_trans]

/--
概要：基底上の射が誘導する局所係数の単体的群の写像。
方針：可換性からの係数の輸送を Kan 拡張し、基底の写像の誘導射へ合成する。
規約：各対象の係数は固定した基底の係数の引き戻し。
使われ方：slice 圏の局所係数の複体。
-/
def overLocalCoefficientSimplicialMap {B : SSet.{u}} (L : LocalCoefficientSystem B)
    {X Y : Over B} (f : X ⟶ Y) :
    (coefficientSimplicialFunctor X.left).obj (pullbackLocalCoefficients X.hom L).coefficients ⟶
      (coefficientSimplicialFunctor Y.left).obj (pullbackLocalCoefficients Y.hom L).coefficients :=
  (coefficientSimplicialFunctor X.left).map (overLocalCoefficientSourceIso L f).hom ≫
    localCoefficientSimplicialMap f.left (pullbackLocalCoefficients Y.hom L)

/--
概要：基底上の誘導写像は元の圏の Kan 拡張の単位と整合する。
方針：係数変換の単位の式と基底の写像の単位の式を合成する。
規約：基底との可換性に由来する輸送を右辺に保つ。
使われ方：関手法則と余極限の比較。
-/
@[reassoc] theorem overLocalCoefficientSimplicialMap_unit {B : SSet.{u}}
    (L : LocalCoefficientSystem B) {X Y : Over B} (f : X ⟶ Y) (e : X.left.Elements) :
    ((Functor.Elements.π X.left).leftKanExtensionUnit
      (pullbackLocalCoefficients X.hom L).coefficients).app e ≫
        (overLocalCoefficientSimplicialMap L f).app e.obj =
    (overLocalCoefficientSourceIso L f).hom.app e ≫
      ((Functor.Elements.π Y.left).leftKanExtensionUnit
        (pullbackLocalCoefficients Y.hom L).coefficients).app (f.left.mapElements.obj e) := by
  let u := ((Functor.Elements.π X.left).leftKanExtensionUnit
    (pullbackLocalCoefficients X.hom L).coefficients).app e
  let v := ((Functor.Elements.π X.left).leftKanExtensionUnit
    (pullbackLocalCoefficients f.left (pullbackLocalCoefficients Y.hom L)).coefficients).app e
  let w := ((Functor.Elements.π Y.left).leftKanExtensionUnit
    (pullbackLocalCoefficients Y.hom L).coefficients).app (f.left.mapElements.obj e)
  let t := (overLocalCoefficientSourceIso L f).hom.app e
  let a := ((coefficientSimplicialFunctor X.left).map
    (overLocalCoefficientSourceIso L f).hom).app e.obj
  let b := (localCoefficientSimplicialMap f.left (pullbackLocalCoefficients Y.hom L)).app e.obj
  have ha : u ≫ a = t ≫ v := coefficientSimplicialFunctor_map_unit X.left _ e
  have hb : v ≫ b = w := localCoefficientSimplicialMap_unit f.left _ e
  change u ≫ (a ≫ b) = t ≫ w
  calc
    _ = (u ≫ a) ≫ b := (Category.assoc _ _ _).symm
    _ = (t ≫ v) ≫ b := congrArg (fun q => q ≫ b) ha
    _ = t ≫ w := by rw [Category.assoc, hb]

end SerrePositivity.KST.Comparison
