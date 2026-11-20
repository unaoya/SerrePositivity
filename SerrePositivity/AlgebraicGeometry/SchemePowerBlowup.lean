module


public meta import SerrePositivity.Util.Citation
public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.SchemeBlowup
public import SerrePositivity.AlgebraicGeometry.PowerNaturality

/-!
概要：KST §5 の一般スキーム上の正の冪による blowup の不変性。
方針：アフィン冪比較同型の自然性から局所モデルの図式の自然同型を作り、余極限へ移す。
規約：通常の blowup、正の冪指数を用いる。
使われ方：Lemma 5.6 の古典的部分と Huneke–Swanson 8.1.5・8.2.1 の比較。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
variable {X : Scheme.{u}} (I : X.IdealSheafData)

set_option backward.isDefEq.respectTransparency false in
/--
概要：正の冪を取った中心と元の中心のアフィン blowup 図式は自然同型。
方針：各アフィン上の冪比較同型を成分とし、係数制限に対する自然性を使う。
規約：KST §5、イデアル層の冪の切断は各切断イデアルの冪。
使われ方：一般スキーム上の冪不変性の同型の構成。
-/
def affineBlowupPowerNatIso (n : ℕ) (hn : 0 < n) :
    affineBlowupDiagram (I ^ n) ≅ affineBlowupDiagram I :=
  NatIso.ofComponents (fun U => affineBlowupPowerIso (I.ideal U) n hn) (by
    intro U V h
    have hc : (I.ideal V).map (affineModelRestriction (leOfHom h)) = I.ideal U :=
      I.map_ideal (leOfHom h)
    change affineBlowupCenterMap ((I.ideal V) ^ n) ((I.ideal U) ^ n)
        (affineModelRestriction (leOfHom h))
        (by rw [Ideal.map_pow, hc]) ≫
        (affineBlowupPowerIso (I.ideal V) n hn).hom =
      (affineBlowupPowerIso (I.ideal U) n hn).hom ≫
        affineBlowupCenterMap (I.ideal V) (I.ideal U) (affineModelRestriction (leOfHom h))
          (I.map_ideal (leOfHom h))
    exact affineBlowupPowerIso_naturality (I.ideal V) (I.ideal U)
      (affineModelRestriction (leOfHom h)) (I.map_ideal (leOfHom h)) n hn)

/--
概要：一般スキームの中心の正の冪に沿う blowup は元の blowup と同型。
方針：アフィン局所モデルの図式の自然同型をスキームの余極限へ移す。
規約：KST §5、任意のイデアル層、n > 0。有限生成性・Noether 性は不要。
使われ方：厚みを変える blowup の比較と Lemma 5.6 の古典的入力。
-/
def blowupPowerIso (n : ℕ) (hn : 0 < n) : blowup (I ^ n) ≅ blowup I :=
  HasColimit.isoOfNatIso (affineBlowupPowerNatIso I n hn)

set_option backward.isDefEq.respectTransparency false in
/--
概要：一般の冪比較同型は各アフィン局所モデルの冪比較同型に制限される。
方針：余極限の自然同型の標準射との交換式を使う。
規約：KST §5、同型は Bl(Iⁿ) から Bl(I) へ向かう。
使われ方：冪比較と局所計算の両立。
-/
@[reassoc] theorem blowupAffineι_blowupPowerIso_hom (n : ℕ) (hn : 0 < n)
    (U : X.affineOpens) :
    blowupAffineι (I ^ n) U ≫ (blowupPowerIso I n hn).hom =
      (affineBlowupPowerIso (I.ideal U) n hn).hom ≫ blowupAffineι I U := by
  exact HasColimit.ι_isoOfNatIso_hom (affineBlowupPowerNatIso I n hn) U

set_option backward.isDefEq.respectTransparency false in
/--
概要：一般の冪比較同型は基礎スキーム上の同型。
方針：余極限の標準射で比較し、各アフィンの冪比較の構造射との両立を使う。
規約：KST §5、元の基礎スキーム X への射の等式。
使われ方：古典的 blowup の厚みを変える比較図式。
-/
@[reassoc] theorem blowupPowerIso_hom_base (n : ℕ) (hn : 0 < n) :
    (blowupPowerIso I n hn).hom ≫ blowupπ I = blowupπ (I ^ n) := by
  apply colimit.hom_ext
  intro U
  change blowupAffineι (I ^ n) U ≫ (blowupPowerIso I n hn).hom ≫ blowupπ I =
    blowupAffineι (I ^ n) U ≫ blowupπ (I ^ n)
  rw [blowupAffineι_blowupPowerIso_hom_assoc, blowupAffineι_π, blowupAffineι_π]
  unfold affineBlowupModelToBase affineBlowupModelπ
  rw [← Category.assoc, ← Category.assoc, affineBlowupPowerIso_hom_base]
  rfl

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas










/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Eq (1.7)" (partial := component) "仮定：有限列の普遍チャート、または有限生成中心の正の冪の通常ブローアップ（Lean が強い）。結論：局所チャート同定と通常の冪比較を供給するが、原典の普遍正則列の厚化付きの全塔は含まない（Lean が弱い）。"] _root_.SerrePositivity.AlgebraicGeometry.blowupPowerIso
attribute [cite KST "Eq (5.10)"] _root_.SerrePositivity.AlgebraicGeometry.blowupPowerIso
attribute [cite KST "Eq (5.11)" (partial := component) "仮定：通常ブローアップの整数冪、または指定された普遍 Koszul の底変換（Lean が強い）。結論：イデアルと冪の同型・局所 Koszul 比較。異なる冪列の有限射を導来ブローアップ間に構成する部分は含まない（Lean が弱い）。"] _root_.SerrePositivity.AlgebraicGeometry.blowupPowerIso
attribute [cite KST "Lemma 5.6" (partial := component) "仮定：有限生成の中心と正整数冪の通常ブローアップ（Lean が強い）。結論：通常ブローアップの冪比較を供給する。導来ブローアップの塔でのプロ K の対角比較は含まない（Lean が弱い）。"] _root_.SerrePositivity.AlgebraicGeometry.blowupPowerIso
