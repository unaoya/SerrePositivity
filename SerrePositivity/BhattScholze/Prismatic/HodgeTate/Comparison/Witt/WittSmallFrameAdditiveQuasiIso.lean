module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.CechFrameAdditiveQuasiIso
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittSmallFrame
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittSmallFrame

/-!
# 係数変更後の有限・大きい Witt 分冪枠

## 概要
有限 Witt 分冪模型から大きい枠への比較は、任意の加法的関手で移しても擬同型。

## 方針
有限模型との同型と剰余環の同型は関手で保存され、枠の比較には既存の両合成のホモトピーを使う。

## 規約
関手の完全性や底変換の平坦性は仮定しない。

## 使われ方
BS 著者版 Theorem 6.4、Witt から剰余係数への比較。
-/

public noncomputable section
open CategoryTheory AlgebraicTopology
universe u
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A)
variable (hpC : Function.Injective (fun x : A ⧸ P.ideal => (p : A ⧸ P.ideal) * x))
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A ⧸ P.ideal))
variable [hC : IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal)]
variable (Q : Poly (A ⧸ P.ideal))
variable (hk : IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal))
variable (F : ModuleCat.{u} (WittVector p (A ⧸ P.ideal)) ⥤ ModuleCat.{u} B) [F.Additive]
local notation "C" => A ⧸ P.ideal
local notation "W" => WittVector p C
local notation "γ" => wittPdStructure p C hpC hlocal
local notation "hp" => p_mem_wittPdIdeal p C

omit hC in
/-- 有限・大きい Witt 枠の比較は各項への任意の加法的関手で擬同型を保つ。 -/
theorem wittSmallFrame_map_quasiIso :
    QuasiIso ((F.mapHomologicalComplex _).map
      ((alternatingCofaceMapComplex _).map
        (Functor.whiskerRight (wittSmallFrame P hpC hlocal Q hk)
          (PDCechNerve.algebraModule W)))) := by
  let : Algebra W C := (wZero p C).toAlgebra
  let L := (Functor.whiskeringRight SimplexCategory _ _).obj (PDCechNerve.algebraModule W) ⋙
    alternatingCofaceMapComplex _
  have h : QuasiIso ((F.mapHomologicalComplex _).map (L.map (frameMap P hpC hlocal Q))) :=
    pdCechNerveMap_map_quasiIso p γ hp (bigResidue_ker_witt P Q)
      (smallFrameOnBigResidue P hpC Q) (largeFrame P Q)
      (frameLift P hpC hlocal Q) (frameLift_spec P hpC hlocal Q) F
      (smallFrameOnBigResidue_surjective P hpC Q)
  change QuasiIso ((F.mapHomologicalComplex _).map (L.map (wittSmallFrame P hpC hlocal Q hk)))
  change QuasiIso ((F.mapHomologicalComplex _).map
    (L.map ((smallIso P hpC hlocal Q hk).hom ≫ (smallFrameChangeResidue P hpC hlocal Q).hom ≫
      frameMap P hpC hlocal Q)))
  rw [L.map_comp, L.map_comp, (F.mapHomologicalComplex _).map_comp,
    (F.mapHomologicalComplex _).map_comp]
  infer_instance

end SerrePositivity.BhattScholze.Prismatic
