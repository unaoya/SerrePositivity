module

public import SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
public import SerrePositivity.KST.DerivedGeometry.LinearComplexEnrichment
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Algebra.Homology.Additive

/-!
# 係数加群層の複体の宇宙調整と dg 豊穣

概要：全係数加群層の複体に、既存 dg 商で使える宇宙の dg 構造を与える。
方針：Hom を ULiftHom で一段上げ、持ち上げた整数環上で豊穣する。
規約：元の層複体とは加法的圏同値で比較し、小ささを公理にしない。
使われ方：KST D4・§13 決定11、Drinfeld dg 商、Toën §3.2。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.DerivedGeometry

/--
概要：層複体の全対象を扱う dg 増強の可換な基礎環。
方針：整数環を層の対象の宇宙まで持ち上げる。
規約：係数環層 H_X の置換ではなく加法的豊穣のスカラー環。
使われ方：KST D4・§13 決定11、Drinfeld dg 商の宇宙条件。
-/
abbrev CoefficientDGBase : Type (u + 1) := ULift.{u + 1} ℤ

namespace CoefficientSheaf

variable {X : Scheme.{u}} (B : CoefficientSheaf X)

/--
概要：係数加群層の Hom だけを対象の宇宙まで持ち上げた圏。
方針：Mathlib の ULiftHom を使う。
規約：対象は元の係数加群層と対応する。
使われ方：KST D4、Drinfeld dg 商の小ささ条件。
-/
abbrev LiftedModules := ULiftHom.{u + 1} B.Modules

/--
概要：Hom を持ち上げた係数加群層の圏は加法的。
方針：元の Hom の加法群を ULift に移す。
規約：合成は ULiftHom の既存の合成を使う。
使われ方：KST D4、Toën §3.2 の層複体の写像複体。
-/
instance liftedModulesPreadditive : Preadditive B.LiftedModules where
  homGroup M N := inferInstanceAs (AddCommGroup (ULift.{u + 1} (M.objDown ⟶ N.objDown)))
  add_comp := by
    intro M N K f g h
    apply ULift.ext
    exact (Preadditive.rightComp M.objDown h.down).map_add f.down g.down
  comp_add := by
    intro M N K f g h
    apply ULift.ext
    exact (Preadditive.leftComp K.objDown f.down).map_add g.down h.down

/--
概要：Hom を上へ持ち上げる比較関手は加法的。
方針：加法は成分ごとの ULift で定義されていることを使う。
規約：元の層の射を変更しない。
使われ方：KST D4、Toën §3.2 の元の層複体への比較。
-/
instance liftedUpAdditive : (show B.Modules ⥤ B.LiftedModules from ULiftHom.up).Additive where
  map_add := by intros; rfl

/--
概要：Hom を元へ戻す比較関手は加法的。
方針：ULift.down が加法を保つことを使う。
規約：層複体のコホモロジー条件をこの関手で読む。
使われ方：KST D4、Toën §3.2 の acyclic 条件の比較。
-/
instance liftedDownAdditive : (show B.LiftedModules ⥤ B.Modules from ULiftHom.down).Additive where
  map_add := by intros; rfl

/--
概要：Hom を元へ戻す関手は充満。
方針：ULiftHom の既存の同値の逆関手の完全充満性を使う。
規約：複体とホモトピー圏の比較へこの性質を渡す。
使われ方：KST D4、Toën §3.2 の宇宙調整の検証。
-/
instance liftedDownFull : (show B.LiftedModules ⥤ B.Modules from ULiftHom.down).Full :=
  (ULiftHom.equiv : B.Modules ≌ B.LiftedModules).fullyFaithfulInverse.full

/--
概要：Hom を元へ戻す関手は忠実。
方針：ULiftHom の既存の同値の逆関手の完全充満性を使う。
規約：射の等式を元の層の圏で判定する。
使われ方：KST D4、Toën §3.2 の宇宙調整の検証。
-/
instance liftedDownFaithful : (show B.LiftedModules ⥤ B.Modules from ULiftHom.down).Faithful :=
  (ULiftHom.equiv : B.Modules ≌ B.LiftedModules).fullyFaithfulInverse.faithful

/--
概要：持ち上げた係数加群層の圏は持ち上げた整数環上で線形。
方針：整数による標準加法作用を ULift の環同型に沿って制限する。
規約：追加の線形構造を仮定しない。
使われ方：KST D4、Toën §3.2 の層複体の dg 豊穣。
-/
instance liftedModulesLinear : Linear CoefficientDGBase.{u} B.LiftedModules where
  homModule M N := Module.compHom (M ⟶ N)
    (ULift.ringEquiv : CoefficientDGBase.{u} ≃+* ℤ).toRingHom
  smul_comp M N K r f g := by
    change (r.down • f) ≫ g = r.down • (f ≫ g)
    exact (Preadditive.rightComp M g).map_zsmul r.down f
  comp_smul M N K f r g := by
    change f ≫ (r.down • g) = r.down • (f ≫ g)
    exact (Preadditive.leftComp K f).map_zsmul r.down g

/--
概要：宇宙を調整した係数加群層の非有界コチェイン複体。
方針：持ち上げた Hom の圏の実際の複体を取る。
規約：元の層複体との同値は次の比較で明示する。
使われ方：KST D4・§13 決定11の dg 商の始域。
-/
abbrev Complexes := CochainComplex B.LiftedModules ℤ

/--
概要：元の係数加群層の複体と宇宙調整した複体の圏同値。
方針：ULiftHom の加法的同値を複体へ適用する。
規約：全複体を扱い、各項の準連接性は要求しない。
使われ方：KST D4、Toën §3.2 の実際の層コホモロジーとの接続。
-/
def complexLiftEquivalence : CochainComplex B.Modules ℤ ≌ B.Complexes :=
  (ULiftHom.equiv : B.Modules ≌ B.LiftedModules).mapHomologicalComplex (.up ℤ)

/--
概要：係数層の全複体に既存 DGCategory による dg 構造を与える。
方針：任意の線形加法圏について証明した豊穣を適用する。
規約：Hom と対象の宇宙は持ち上げにより一致させる。
使われ方：KST D4・§13 決定11、Drinfeld dg 商の入力。
-/
instance complexesDGCategory :
    SerrePositivity.DifferentialGraded.DGCategory CoefficientDGBase.{u} B.Complexes :=
  LinearComplex.enrichment

end CoefficientSheaf

end SerrePositivity.KST.DerivedGeometry
