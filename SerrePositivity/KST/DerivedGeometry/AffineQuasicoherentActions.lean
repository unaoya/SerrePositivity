module

public import SerrePositivity.KST.DerivedGeometry.AffineQuasicoherentSections
public import SerrePositivity.KST.DerivedGeometry.CoefficientConstantAction

/-!
# アフィン上での大域係数線形性の判定

概要：基礎 O 加群の射が大域切断上で H 線形なら、各定数係数作用と層全体で可換。
方針：二つの合成の大域切断を比較し、準連接な始域での射の判定を使う。
規約：全係数環層の作用への線形性は局所テンソル比較による別の段階。
使われ方：KST D4・T1′、Toën Derived Azumaya §3.2 のアフィン比較の充満性。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.DerivedGeometry

variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]

/--
概要：大域切断上で H 線形な O 加群層の射は定数係数の作用と可換。
方針：二つの合成を大域切断で比較し、準連接な始域からの射の忠実性を使う。
規約：始域だけに準連接性を要求する。
使われ方：KST D4・T1′、Toën §3.2 の係数線形な射の再構成。
-/
lemma affineUnderlyingHom_commutesConstant
    {M N : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules}
    [((tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget.obj M).IsQuasicoherent]
    (φ : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget.obj M ⟶
      (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget.obj N)
    (hφ : ∀ h : H, ∀ m : M.val.obj (.op ⊤),
      (φ.val.app (.op ⊤)).hom
          (((tensorCoefficientConstant H (Scheme.ΓSpecIso R).inv.hom).app (.op ⊤) h) • m) =
        ((tensorCoefficientConstant H (Scheme.ΓSpecIso R).inv.hom).app (.op ⊤) h) •
          (show N.val.obj (.op ⊤) from (φ.val.app (.op ⊤)).hom m))
    (h : H) :
    coefficientConstantAction H (Scheme.ΓSpecIso R).inv.hom M h ≫ φ =
      φ ≫ coefficientConstantAction H (Scheme.ΓSpecIso R).inv.hom N h := by
  apply affineUnderlyingHom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change M.val.obj (.op ⊤) at m
  exact hφ h m

end SerrePositivity.KST.DerivedGeometry
