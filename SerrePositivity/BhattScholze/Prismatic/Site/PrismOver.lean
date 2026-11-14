module
public import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prism.Basic.Bounded

public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# 向き付き有界 prism の古典的な圏

## 概要
有界な向き付き prism の上で、固定した剰余環の代数を持つ対象とその射を定める。

## 方針
射は向き付き prism の射で、基底および剰余環からの射と可換するもの。

## 規約
環の向きで圏を作り、台の濃度の上限は引数に取る。

## 使われ方
多項式環の Čech–Alexander 模型と、その各項の基底環上の代数。
-/

@[expose] public section
noncomputable section

universe u
open CategoryTheory
open scoped Cardinal

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime]

/-! ## 有界 prism -/

variable {A : Type u} [CommRing A] (P : OrientedPrism p A) (hP : IsBoundedPrism P)
variable (R : Type u) [CommRing R] [Algebra (A ⧸ P.ideal) R]

/-! ## prismatic site の濃度の制限（BS 著者版 Definition 4.1 のための小ささの設定） -/

/-- 概要：site の対象の濃度の上限 κ = (#A + #R + ℵ₀)^{ℵ₀}。
方針：κ^{ℵ₀} = κ なので、Čech–Alexander 複体・完備テンソル・完全化・André 拡大・p 冪根の添加で閉じる（a0-design §2.7）。
規約：定義にパラメータとして残し、κ 不変性は定理（O_Δ についてだけ）。
使われ方：`PrismOver` の対象の条件、本質的小ささ。 -/
def cutoff (A R : Type u) : Cardinal.{u} := (Cardinal.mk A + Cardinal.mk R + ℵ₀) ^ ℵ₀

/-- 概要：許容する切り落とし：κ ≥ cutoff かつ κ^{ℵ₀} = κ（完備テンソル・完備化・可算反復で閉じるための条件。W9-I-11：κ ≥ cutoff だけでは κ^{ℵ₀} = κ は従わない）。
方針：site の公理（押し出しが切り落としに残る）と κ 比較の定理はこの仮定で述べる。`cutoff` 自身は満たす。
規約：—
使われ方：`flatTopology_refine`、`prismaticCohomology_cutoff_invariant`。 -/
def IsAdmissibleCutoff (_P : OrientedPrism p A) (R : Type u) (κ : Cardinal.{u}) : Prop := cutoff A R ≤ κ ∧ κ ^ ℵ₀ = κ

/-! ## 対象と射（Def 4.1 の圏、環の側） -/

/-- 概要：(R/A)_Δ の対象（環の側）：(A,(d)) 上の有界向き付き prism (B, dB) と A/d 代数の射 R → B/dB。濃度 ≤ κ（BS 著者版 Definition 4.1 の affine の場合）。
方針：prism の射 `OrientedPrism.Hom P Q` で、剛性により Q.ideal = (d)B（`Hom.map_ideal_eq`）。R からの写像は商への A/d 代数射。
規約：原典は (B, IB) と Spf(B/IB) → X。affine の R に限る。κ は明示のパラメータ。
使われ方：site の対象。 -/
structure PrismOver (κ : Cardinal.{u}) where
  /-- 台の環。 -/
  B : Type u
  [ring : CommRing B]
  /-- (B, dB) の向き付き prism 構造。 -/
  Q : OrientedPrism p B
  /-- 有界。 -/
  bounded : IsBoundedPrism Q
  /-- (A,(d)) → (B, dB) の prism の射。 -/
  toHom : OrientedPrism.Hom P Q
  /-- R → B/dB。A/d 代数の射（B/dB の A/d 代数構造は `toHom.quotientMap`）。 -/
  sec : R →+* B ⧸ Q.ideal
  /-- sec は A/d 線形：sec ∘ (A/d → R) = toHom.quotientMap。 -/
  sec_comp : sec.comp (algebraMap (A ⧸ P.ideal) R) = toHom.quotientMap
  /-- 濃度 ≤ κ。 -/
  small : Cardinal.mk B ≤ κ

attribute [instance] PrismOver.ring
namespace PrismOver

variable {P R} {κ : Cardinal.{u}}

/-- 概要：(R/A)_Δ の射（環の側）：prism の射で、A からの射と R からの写像の両方と両立するもの。
方針：`OrientedPrism.Hom` に二つの可換条件を足す。
規約：原典の「obvious」な射。
使われ方：圏の構造。 -/
structure Hom (X Y : PrismOver P R κ) where
  /-- 下にある prism の射。 -/
  toHom : OrientedPrism.Hom X.Q Y.Q
  /-- A 上の射。 -/
  comm_base : toHom.comp X.toHom = Y.toHom
  /-- R からの写像と両立。 -/
  comm_sec : toHom.quotientMap.comp X.sec = Y.sec

/-- 基底および剰余環の可換条件を持つ射は、台の prism 射で決まる。 -/
@[ext]
theorem Hom.ext {X Y : PrismOver P R κ} {f g : Hom X Y} (h : f.toHom = g.toHom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category (PrismOver P R κ) where
  Hom := Hom
  id X := ⟨OrientedPrism.Hom.id X.Q, by simp, by simp⟩
  comp f g := ⟨g.toHom.comp f.toHom, by
    rw [OrientedPrism.Hom.comp_assoc, f.comm_base, g.comm_base], by
    rw [OrientedPrism.Hom.quotientMap_comp, RingHom.comp_assoc, f.comm_sec, g.comm_sec]⟩
  id_comp f := Hom.ext (OrientedPrism.Hom.comp_id f.toHom)
  comp_id f := Hom.ext (OrientedPrism.Hom.id_comp f.toHom)
  assoc f g h := Hom.ext (OrientedPrism.Hom.comp_assoc h.toHom g.toHom f.toHom).symm

end PrismOver

/-- 概要：対象の台の環と基底からの構造射を取る関手。
方針：射の基底上の可換性を `Under` の射に移す。
規約：環の向きを保つ。
使われ方：Čech–Alexander 模型を余単体的な基底代数として読む。 -/
def prismSiteAlgebras (S : Type u) [CommRing S] [Algebra (A ⧸ P.ideal) S] (κ : Cardinal.{u}) :
    PrismOver P S κ ⥤ Under (CommRingCat.of A) where
  obj X := Under.mk (CommRingCat.ofHom X.toHom.toRingHom)
  map f := Under.homMk (CommRingCat.ofHom f.toHom.toRingHom) (by
    apply CommRingCat.hom_ext
    exact congrArg OrientedPrism.Hom.toRingHom f.comm_base)
  map_id X := Under.UnderMorphism.ext rfl
  map_comp f g := Under.UnderMorphism.ext rfl

end SerrePositivity.BhattScholze.Prismatic

/-! Reviewed literature correspondences. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Def 1.6" (partial := special) "Def 4.1 の言い直し。本体の PrismOver は向き付き有界基底・κ-small の対象（drafts と同じ形、11-11 に地図を訂正）。site の層と RΓ は drafts"] _root_.SerrePositivity.BhattScholze.Prismatic.PrismOver
attribute [cite BS19 "Def 4.1" (partial := special) "affine・向き付き・濃度 ≤ κ の site と平坦位相、構造層が層であること（BS-W15 K4）。RΓ_Δ（Čech–Alexander による計算）は G10 待ち ／ 11-11 更新（2）"] _root_.SerrePositivity.BhattScholze.Prismatic.PrismOver
