module

public import SerrePositivity.KST.DerivedGeometry.CoefficientSheaf

/-!
# 係数加群層の忘却の忠実性と保存性

概要：実際の係数忘却が忠実で同型を反映することを証明する。
方針：スカラー制限の忠実性と基礎アーベル群の層を使う。
規約：H の平坦性を要求しない。導来圏での生成は別途証明する。
使われ方：KST T1、Bondal–van den Bergh Thm 3.1.1 の係数版、Toën §3.2。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.DerivedGeometry.CoefficientSheaf

variable {X : Scheme.{u}} (B : CoefficientSheaf X)

/--
概要：係数忘却は忠実。
方針：前層への忘却とスカラー制限の忠実性に帰着する。
規約：係数環の可換性・平坦性を要求しない。
使われ方：KST T1、Toën §3.2 の自由・忘却随伴の構成。
-/
instance forget_faithful : B.forget.Faithful where
  map_injective {M N} f g h := by
    apply SheafOfModules.hom_ext
    apply (PresheafOfModules.restrictScalars B.structureMap.hom).map_injective
    exact congrArg SheafOfModules.Hom.val h

/--
概要：係数忘却は同型を反映する。
方針：係数を忘れても基礎アーベル群の層の射は変わらないことを使う。
規約：層の圏での主張であり、導来忘却の構成とは区別する。
使われ方：KST T1、Toën §3.2 の保存的な忘却関手の基礎。
-/
instance forget_reflectsIsomorphisms : B.forget.ReflectsIsomorphisms where
  reflects {M N} f h := by
    letI := PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpCatToSheaf_1
      (R := B.ring)
    have hmap : IsIso (((SheafOfModules.toSheaf B.ring) ⋙
        sheafToPresheaf _ _).map f) :=
      Functor.map_isIso (Scheme.Modules.toPresheaf X) (B.forget.map f)
    letI : IsIso ((sheafToPresheaf _ _).map ((SheafOfModules.toSheaf B.ring).map f)) := hmap
    letI : IsIso ((SheafOfModules.toSheaf B.ring).map f) :=
      isIso_of_reflects_iso ((SheafOfModules.toSheaf B.ring).map f) (sheafToPresheaf _ _)
    exact isIso_of_reflects_iso f (SheafOfModules.toSheaf B.ring)

end SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
