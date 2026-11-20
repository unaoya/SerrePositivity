module

public import SerrePositivity.AlgebraicGeometry.SchemeBlowup

/-!
概要：KST §5 の一般の blowup と各アフィン開集合上の Rees Proj の比較。
方針：標準射の像を構造射の逆像と同定し、開部分スキームの同型を構成する。
規約：基礎スキームの分離性は不要。
使われ方：固有性、例外因子、中心外同型、冪不変性の大域化。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {X : Scheme.{u}} (I : X.IdealSheafData)

set_option backward.isDefEq.respectTransparency false in
/--
概要：局所モデルから一般の blowup への標準射の像は、対応するアフィン開集合の逆像全体。
方針：別の局所モデルで表示した点を共通基本開近傍のモデルへ持ち上げる。
規約：KST §5、点集合の像の等式を先に示す。
使われ方：各アフィン開集合上の blowup のスキーム同型。
-/
theorem blowupAffineι_range (U : X.affineOpens) :
    Set.range (blowupAffineι I U) = (blowupπ I ⁻¹ᵁ U.1).carrier := by
  apply Set.Subset.antisymm
  · rintro _ ⟨y, rfl⟩
    change (blowupAffineι I U ≫ blowupπ I) y ∈ U.1
    rw [blowupAffineι_π]
    exact affineBlowupModelToBase_mem I U y
  · intro x hx
    obtain ⟨V, y, hy⟩ := exists_blowupAffineι I x
    have hyU : affineBlowupModelToBase I V y ∈ U.1 := by
      rw [← blowupAffineι_π]
      change blowupπ I (blowupAffineι I V y) ∈ U.1
      rw [hy]
      exact hx
    obtain ⟨f, g, hfg, hyf⟩ := exists_basicOpen_le_affine_inter U.2 V.2
      (affineBlowupModelToBase I V y) ⟨hyU, affineBlowupModelToBase_mem I V y⟩
    let W := X.affineBasicOpen f
    let hWU : W ≤ U := X.affineBasicOpen_le f
    let hWV : W ≤ V := hfg.trans_le (X.basicOpen_le g)
    have hyg : y ∈ (affineBlowupModelToBase I V ⁻¹ᵁ X.basicOpen g).carrier := hfg ▸ hyf
    rw [← affineBlowupModelMap_range_of_eq_basicOpen I hWV g (Subtype.ext hfg)] at hyg
    obtain ⟨w, hw⟩ := hyg
    refine ⟨affineBlowupModelMap I hWU w, ?_⟩
    calc
      _ = (affineBlowupModelMap I hWU ≫ blowupAffineι I U) w := rfl
      _ = blowupAffineι I W w := by rw [affineBlowupModelMap_blowupAffineι]
      _ = (affineBlowupModelMap I hWV ≫ blowupAffineι I V) w := by
        rw [affineBlowupModelMap_blowupAffineι]
      _ = blowupAffineι I V y := congrArg (blowupAffineι I V) hw
      _ = x := hy

set_option backward.isDefEq.respectTransparency false in
/--
概要：アフィン局所モデルは一般の blowup の対応する逆像開部分スキームと同型。
方針：二つの開埋め込みの像の一致から同型を構成する。
規約：KST §5、通常の Rees Proj と実際の開部分スキームの同型。
使われ方：アフィンで証明した性質を一般の blowup へ移す。
-/
def blowupAffineIso (U : X.affineOpens) :
    affineBlowupModel I U ≅ (blowupπ I ⁻¹ᵁ U.1).toScheme :=
  IsOpenImmersion.isoOfRangeEq (blowupAffineι I U) (blowupπ I ⁻¹ᵁ U.1).ι
    ((blowupAffineι_range I U).trans (Scheme.Opens.range_ι _).symm)

/--
概要：局所モデルの比較同型と逆像開集合の包含の合成は標準射。
方針：像の一致から得た同型の因子化公式を適用する。
規約：KST §5、一般の blowup への射の等式。
使われ方：構造射の制限と局所モデル上の構造射を比較する。
-/
@[reassoc] theorem blowupAffineIso_hom_ι (U : X.affineOpens) :
    (blowupAffineIso I U).hom ≫ (blowupπ I ⁻¹ᵁ U.1).ι = blowupAffineι I U :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _
    ((blowupAffineι_range I U).trans (Scheme.Opens.range_ι _).symm)

set_option backward.isDefEq.respectTransparency false in
/--
概要：局所モデルの比較同型はアフィン開集合上の構造射と両立する。
方針：標的の開包含を消去し、標準射と構造射の交換式を使う。
規約：KST §5、構造射の制限そのものとの等式。
使われ方：固有性と中心外同型をアフィン局所的に移す。
-/
@[reassoc] theorem blowupAffineIso_hom_restrict (U : X.affineOpens) :
    (blowupAffineIso I U).hom ≫ (blowupπ I ∣_ U.1) = affineBlowupModelπ I U := by
  apply (cancel_mono U.1.ι).mp
  rw [Category.assoc, morphismRestrict_ι, blowupAffineIso_hom_ι_assoc, blowupAffineι_π]
  rfl

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
