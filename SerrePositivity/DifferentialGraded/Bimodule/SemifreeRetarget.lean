module
public import SerrePositivity.DifferentialGraded.Bimodule.SemifreeResolution

/-! # 準同型による増大の後合成でsemifree解像度の終域を替える

## 概要
準同型による増大の後合成でsemifree解像度の終域を替える。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleSemifreeResolution
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]

/-- sourceとfiltrationを保持し、増大を指定準同型で後合成する。 -/
def postcompose {M N : BimoduleCategory A B C} (R : BimoduleSemifreeResolution A B C M)
    (f : M ⟶ N) (hf : BimoduleCategory.quasiIso A B C f) :
    BimoduleSemifreeResolution A B C N where
  source := R.source
  filtration := R.filtration
  π := R.π ≫ f
  quasiIso := (BimoduleCategory.quasiIso A B C).comp_mem _ _ R.quasiIso hf

lemma postcompose_obj {M N : BimoduleCategory A B C} (R : BimoduleSemifreeResolution A B C M)
    (f : M ⟶ N) (hf : BimoduleCategory.quasiIso A B C f) :
    (postcompose A B C R f hf).obj = R.obj := rfl

end SerrePositivity.DifferentialGraded.BimoduleSemifreeResolution
