module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prismatic.Site.PrismOver
public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# affine big 結晶サイトの対象と射

## 概要
分冪基底 (k,J,γ) 上の p 冪零な厚化と、剰余代数からの射を定める。

## 方針
環の向きで圏を作る。分冪射の合成と剰余の可換条件で圏の公理を示す。

## 規約
big site なので剰余への射は同型を要求しない。濃度の上限を引数に残す。

## 使われ方
BS 著者版 Theorem 5.2、Berthelot III.4、Stacks 07HM。Zariski 位相と分冪 Čech の塔の入口。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open scoped Cardinal
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ)

/-- 結晶サイトの濃度の上限。pd 包・有限余積・局所化・有限冪商を扱うために使う。 -/
def IsCrystallineCutoff (k R : Type u) (κ : Cardinal.{u}) : Prop := cutoff k R ≤ κ

section Site

variable {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J)
variable (R : Type u) [CommRing R] [Algebra (k ⧸ J) R]

/-- 分冪基底上の p 冪零な affine 厚化と剰余代数の構造射。
Berthelot III.4、Stacks 07HM の big site の環の向き。構造射は任意の環射。 -/
structure CrysOver (κ : Cardinal.{u}) where
  /-- 台の環。 -/
  B : Type u
  [ring : CommRing B]
  [alg : Algebra k B]
  /-- pd イデアル。 -/
  JB : Ideal B
  /-- divided powers。 -/
  δ : DividedPowers JB
  /-- k → B は pd 射。 -/
  base_dp : DividedPowers.IsDPMorphism γ δ (algebraMap k B)
  /-- p は冪零（Berthelot の site の対象は p 冪零の S スキーム上）。 -/
  nilpotent : IsNilpotent (p : B)
  /-- R → B/J_B。 -/
  sec : R →+* B ⧸ JB
  /-- sec は k 線形：k → k/J → R → B/J_B は k → B → B/J_B。 -/
  sec_comp : sec.comp ((algebraMap (k ⧸ J) R).comp (Ideal.Quotient.mk J)) =
    (Ideal.Quotient.mk JB).comp (algebraMap k B)
  /-- 濃度 ≤ κ。 -/
  small : Cardinal.mk B ≤ κ

attribute [instance] CrysOver.ring CrysOver.alg

namespace CrysOver

variable {γ R} {κ : Cardinal.{u}}

/-- 概要：(R/k)_CRYS の射（環の側）：pd 射である k 代数の射で、R からの写像と両立するもの（Stacks Tag 07HM (2)）。
方針：両立は「B/J_B で sec r の代表は sec r の代表へ」の形で（商写像の誘導を型に出さない）。
規約：site の射はこの opposite。
使われ方：圏の構造。 -/
structure Hom (X Y : CrysOver p γ R κ) where
  /-- 下にある k 代数の射。 -/
  toAlgHom : X.B →ₐ[k] Y.B
  /-- pd 射。 -/
  dp : DividedPowers.IsDPMorphism X.δ Y.δ toAlgHom.toRingHom
  /-- R からの写像と両立。 -/
  comm_sec : ∀ (r : R) (b : X.B), Ideal.Quotient.mk X.JB b = X.sec r →
    Ideal.Quotient.mk Y.JB (toAlgHom b) = Y.sec r

/-- 分冪と剰余の両立は命題なので、射は台の代数射で決まる。 -/
@[ext] theorem Hom.ext {X Y : CrysOver p γ R κ} {f g : Hom p X Y}
    (h : f.toAlgHom = g.toAlgHom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category (CrysOver p γ R κ) where
  Hom := Hom p
  id X := ⟨AlgHom.id k X.B,
    ⟨by simp, fun _ _ => rfl⟩, fun _ _ h => h⟩
  comp f g := ⟨g.toAlgHom.comp f.toAlgHom, g.dp.comp _ f.dp,
    fun r b h => g.comm_sec r _ (f.comm_sec r b h)⟩
  id_comp f := Hom.ext p rfl
  comp_id f := Hom.ext p rfl
  assoc f g h := Hom.ext p rfl


end CrysOver

/-- 基底環の下の環として結晶厚化の台を読む。 -/
def crysAlgebras (κ : Cardinal.{u}) :
    CrysOver p γ R κ ⥤ Under (CommRingCat.of k) where
  obj X := Under.mk (CommRingCat.ofHom (algebraMap k X.B))
  map f := Under.homMk (CommRingCat.ofHom f.toAlgHom.toRingHom) (by
    apply CommRingCat.hom_ext
    exact RingHom.ext f.toAlgHom.commutes)
  map_id X := Under.UnderMorphism.ext rfl
  map_comp f g := Under.UnderMorphism.ext rfl

end Site
end SerrePositivity.BhattScholze.Prismatic

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Notation 5.1" (partial := component) "BS-D69 P3（11-12）：結晶サイトの古典的な部分（big affine site の対象と射、Zariski 位相、構造環の層性、Čech の塔と pro 弱終性）は本体。pd イデアル I ∋ p の一般形と Frobenius の捻り R^(1) は本体にない（drafts の crystallineComparison_polynomial は一般の結晶 prism と I ∋ p の多項式を扱う） ／ 11-12 夜更新（§5・§6 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.CrysOver
attribute [cite BS19 "Notation 5.1" (partial := component) "BS-D69 P3（11-12）：結晶サイトの古典的な部分（big affine site の対象と射、Zariski 位相、構造環の層性、Čech の塔と pro 弱終性）は本体。pd イデアル I ∋ p の一般形と Frobenius の捻り R^(1) は本体にない（drafts の crystallineComparison_polynomial は一般の結晶 prism と I ∋ p の多項式を扱う） ／ 11-12 夜更新（§5・§6 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.crysAlgebras
