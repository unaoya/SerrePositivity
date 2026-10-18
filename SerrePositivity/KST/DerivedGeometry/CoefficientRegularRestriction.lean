module

public import SerrePositivity.KST.DerivedGeometry.CoefficientRestriction
public import SerrePositivity.KST.DerivedGeometry.CoefficientRegularMap

/-!
# 正則構造層加群と開制限

概要：係数環層を制限して作る正則 O 加群と、正則 O 加群を制限したものを比較する。
方針：基礎加法群の恒等写像に、開部分の構造層の作用との両立を添える。
規約：Mathlib の開埋め込みに沿う加群の制限関手を使う。
使われ方：KST D4、Toën Derived Azumaya §3.2 の局所的な準連接性。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.DerivedGeometry.CoefficientSheaf

variable {X : Scheme.{u}} (B : CoefficientSheaf X) (U : X.Opens)

/--
概要：正則 O 加群の制限から、制限した係数環層の正則 O 加群への標準射。
方針：開像の切断上の恒等写像が構造層の作用を保つことを確認する。
規約：開部分の包含の切断環の同型を明示する。
使われ方：KST D4、Toën §3.2 の正則加群の局所模型の比較。
-/
def regularRestrictMap :
    (Scheme.Modules.restrictFunctor U.ι).obj B.regular ⟶ (B.restrict U).regular where
  val := PresheafOfModules.homMk (𝟙 _) (fun V r x => by
    change B.ring.obj.obj (.op (U.ι ''ᵁ V.unop)) at x
    change B.structureMap.hom.app (.op (U.ι ''ᵁ V.unop))
        ((U.ι.appIso V.unop).inv r) * x =
      B.structureMap.hom.app (.op (U.ι ''ᵁ V.unop)) r * x
    rw [Scheme.Opens.ι_appIso]
    rfl)

/--
概要：正則加群と開制限の比較射は同型。
方針：加法群の層に忘れると恒等射になることを使う。
規約：構造層上の線形性は比較射の構成で証明する。
使われ方：KST D4、Toën §3.2 の準連接性の局所判定への接続。
-/
instance regularRestrictMap_isIso : IsIso (regularRestrictMap B U) := by
  let := PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpCatToSheaf_1
    (R := U.toScheme.ringCatSheaf)
  have : IsIso ((SheafOfModules.toSheaf U.toScheme.ringCatSheaf).map
      (regularRestrictMap B U)) := by
    change IsIso (𝟙 _)
    infer_instance
  exact isIso_of_reflects_iso (regularRestrictMap B U)
    (SheafOfModules.toSheaf U.toScheme.ringCatSheaf)

/--
概要：正則 O 加群の形成と開部分への制限は標準的に可換。
方針：構成した恒等切断上の比較射を同型として束ねる。
規約：層の切断上の一致を O 加群の同型として明示する。
使われ方：KST D4、Toën §3.2 の係数環層の局所比較。
-/
def regularRestrictIso :
    (Scheme.Modules.restrictFunctor U.ι).obj B.regular ≅ (B.restrict U).regular :=
  asIso (regularRestrictMap B U)

end SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
