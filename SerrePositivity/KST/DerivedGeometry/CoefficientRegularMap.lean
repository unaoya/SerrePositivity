module

public import SerrePositivity.KST.DerivedGeometry.AffineCoefficientModule

/-!
# 係数環層の射と正則構造層加群

概要：構造層射と可換な係数環層の射から正則 O 加群の射を構成する。
方針：基礎加法群の射に、構造層の作用との両立を添える。
規約：環の可換性を要求しない。
使われ方：KST D4、Toën Derived Azumaya §3.2 の係数底変換。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.DerivedGeometry.CoefficientSheaf

variable {X : Scheme.{u}} {B C : CoefficientSheaf X}
  (φ : B.ring ⟶ C.ring) (hφ : B.structureMap ≫ φ = C.structureMap)

/--
概要：構造層の作用を保つ係数環層の射は正則 O 加群の射を与える。
方針：加法的な前層射に構造層上の線形性を添える。
規約：正則加群は左加群とする。
使われ方：KST D4、Toën §3.2 の正則加群の係数比較。
-/
def regularMap : B.regular ⟶ C.regular where
  val := PresheafOfModules.homMk
    (show B.regular.val.presheaf ⟶ C.regular.val.presheaf from
      Functor.whiskerRight φ.hom (forget₂ RingCat AddCommGrpCat))
    (fun U r x => by
      change B.ring.obj.obj U at x
      change φ.hom.app U (B.structureMap.hom.app U r * x) =
        C.structureMap.hom.app U r * φ.hom.app U x
      rw [map_mul]
      have hr := congrArg (fun g => g.hom.app U r) hφ
      change φ.hom.app U (B.structureMap.hom.app U r) = C.structureMap.hom.app U r at hr
      rw [hr])

/--
概要：係数環層の同型から得る正則 O 加群の比較射は同型。
方針：基礎加法群の層への忠実な忘却で同型性を反映する。
規約：構造層の射との可換性を仮定として明示する。
使われ方：KST D4、Toën §3.2 の正則加群の準連接性の移送。
-/
instance regularMap_isIso [IsIso φ] : IsIso (regularMap φ hφ) := by
  let := PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpCatToSheaf_1
    (R := X.ringCatSheaf)
  have : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map (regularMap φ hφ)) := by
    change IsIso ((sheafCompose _ (forget₂ RingCat AddCommGrpCat)).map φ)
    infer_instance
  exact isIso_of_reflects_iso (regularMap φ hφ) (SheafOfModules.toSheaf X.ringCatSheaf)

end SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
