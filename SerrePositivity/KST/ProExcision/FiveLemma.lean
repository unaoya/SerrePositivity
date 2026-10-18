module

public import SerrePositivity.KST.ProExcision.ModulePro
public import Mathlib.Algebra.Exact.Basic

@[expose] public section

/-!
# 塔の pro 五項補題

概要：レベルごとの完全列の可換図式で中央射の pro 同型を証明する。
方針：核と余核を別々に diagram chase し、Artin–Mazur 判定へ戻す。
規約：レベルごとの縦射を同型とは仮定しない。
使われ方：正本 §2.6 L2、KST §4 の fiber 比較と有理化。
-/

universe u

namespace SerrePositivity.KST.ProExcision

open CategoryTheory

variable (R : Type u) [Ring R]

/-- 概要：五つの加群の塔からなるレベル完全列。
方針：四つのレベル射と三箇所の完全性を持たせる。
規約：両端の単射性・全射性は要求しない。
使われ方：正本 §2.6 L1・L2 の長完全列の五項部分。 -/
structure FiveTerm where
  A : Tower (ModuleCat.{u} R)
  B : Tower (ModuleCat.{u} R)
  C : Tower (ModuleCat.{u} R)
  D : Tower (ModuleCat.{u} R)
  E : Tower (ModuleCat.{u} R)
  ab : LevelHom A B
  bc : LevelHom B C
  cd : LevelHom C D
  de : LevelHom D E
  exactB : ∀ n, Function.Exact (ab.app n).hom (bc.app n).hom
  exactC : ∀ n, Function.Exact (bc.app n).hom (cd.app n).hom
  exactD : ∀ n, Function.Exact (cd.app n).hom (de.app n).hom

variable {R}

/-- 概要：二つの五項完全列間の可換図式。
方針：各縦レベル射と四つの四角形を明示する。
規約：四角形の可換性を元で記述。使われ方：pro 五項補題の入力。 -/
structure FiveTermHom (X Y : FiveTerm R) where
  a : LevelHom X.A Y.A
  b : LevelHom X.B Y.B
  c : LevelHom X.C Y.C
  d : LevelHom X.D Y.D
  e : LevelHom X.E Y.E
  comm_ab : ∀ n x, (b.app n).hom ((X.ab.app n).hom x) =
    (Y.ab.app n).hom ((a.app n).hom x)
  comm_bc : ∀ n x, (c.app n).hom ((X.bc.app n).hom x) =
    (Y.bc.app n).hom ((b.app n).hom x)
  comm_cd : ∀ n x, (d.app n).hom ((X.cd.app n).hom x) =
    (Y.cd.app n).hom ((c.app n).hom x)
  comm_de : ∀ n x, (e.app n).hom ((X.de.app n).hom x) =
    (Y.de.app n).hom ((d.app n).hom x)

namespace FiveTermHom

/-- 概要：五項補題の pro 単射側。
方針：右隣の核を消して持ち上げ、左端の全射で補正して左隣の核を消す。
規約：左端は pro 全射、左右の隣は pro 単射で足りる。
使われ方：正本 §2.6 L2。 -/
theorem isProMono {X Y : FiveTerm R} (f : FiveTermHom X Y)
    (ha : IsProEpi f.a) (hb : IsProMono f.b) (hd : IsProMono f.d) :
    IsProMono f.c := by
  intro n
  obtain ⟨s, hns, hs⟩ := hb n
  obtain ⟨t, hst, ht⟩ := ha s
  obtain ⟨k, htk, hk⟩ := hd t
  refine ⟨k, (hns.trans hst).trans htk, fun x hx ↦ ?_⟩
  have hz : (X.D.transition htk).hom ((X.cd.app k).hom x) = 0 := by
    apply hk
    rw [f.comm_cd, hx, map_zero]
  have hxt : (X.cd.app t).hom ((X.C.transition htk).hom x) = 0 := by
    rw [X.cd.naturality_apply, hz]
  obtain ⟨y, hy⟩ := (X.exactC t _).mp hxt
  have hby : (Y.bc.app t).hom ((f.b.app t).hom y) = 0 := by
    rw [← f.comm_bc, hy, f.c.naturality_apply, hx, map_zero]
  obtain ⟨z, hz⟩ := (Y.exactB t _).mp hby
  obtain ⟨w, hw⟩ := ht z
  let v := (X.B.transition hst).hom y - (X.ab.app s).hom w
  have hv : (f.b.app s).hom v = 0 := by
    dsimp [v]
    rw [map_sub, f.b.naturality_apply, f.comm_ab, hw,
      Y.ab.naturality_apply, hz, sub_self]
  have hvn := hs v hv
  have hbn : (X.B.transition (hns.trans hst)).hom y =
      (X.ab.app n).hom ((X.A.transition hns).hom w) := by
    dsimp [v] at hvn
    rw [map_sub, ← X.ab.naturality_apply, X.B.transition_apply] at hvn
    exact sub_eq_zero.mp hvn
  have hcn := congrArg (fun q ↦ (X.bc.app n).hom q) hbn
  rw [X.bc.naturality_apply, hy, X.C.transition_apply,
    (X.exactB n).apply_apply_eq_zero] at hcn
  exact hcn

/-- 概要：五項補題の pro 全射側。
方針：右隣で持ち上げて右端の核を消し、中央の持ち上げの差を左隣で補正する。
規約：左隣と右隣は pro 全射、右端は pro 単射で足りる。
使われ方：正本 §2.6 L2。 -/
theorem isProEpi {X Y : FiveTerm R} (f : FiveTermHom X Y)
    (hb : IsProEpi f.b) (hd : IsProEpi f.d) (he : IsProMono f.e) :
    IsProEpi f.c := by
  intro n
  obtain ⟨s, hns, hs⟩ := hb n
  obtain ⟨t, hst, ht⟩ := he s
  obtain ⟨k, htk, hk⟩ := hd t
  refine ⟨k, (hns.trans hst).trans htk, fun y ↦ ?_⟩
  obtain ⟨z, hz⟩ := hk ((Y.cd.app k).hom y)
  have hzt : (f.e.app t).hom ((X.de.app t).hom z) = 0 := by
    rw [f.comm_de, hz, Y.de.naturality_apply,
      (Y.exactD k).apply_apply_eq_zero, map_zero]
  have hzs : (X.de.app s).hom ((X.D.transition hst).hom z) = 0 := by
    rw [X.de.naturality_apply]
    exact ht _ hzt
  obtain ⟨w, hw⟩ := (X.exactD s _).mp hzs
  let v := (Y.C.transition (hst.trans htk)).hom y - (f.c.app s).hom w
  have hv : (Y.cd.app s).hom v = 0 := by
    dsimp [v]
    rw [map_sub, Y.cd.naturality_apply, ← f.comm_cd, hw,
      f.d.naturality_apply, hz, Y.D.transition_apply, sub_self]
  obtain ⟨q, hq⟩ := (Y.exactC s _).mp hv
  obtain ⟨b, hb⟩ := hs q
  refine ⟨(X.C.transition hns).hom w + (X.bc.app n).hom b, ?_⟩
  rw [map_add, f.c.naturality_apply, f.comm_bc, hb, Y.bc.naturality_apply, hq]
  dsimp [v]
  rw [map_sub, Y.C.transition_apply]
  exact add_sub_cancel _ _

/-- 概要：加群の塔の pro 五項補題。
方針：中央射の核と余核を eventual に零化し、像への降下で逆射を構成する。
規約：外側四射の pro 同型だけを仮定する。
使われ方：正本 §2.6 L2、KST §4 の完全列の比較。 -/
theorem isProIso {X Y : FiveTerm R} (f : FiveTermHom X Y)
    (ha : IsProIso f.a) (hb : IsProIso f.b)
    (hd : IsProIso f.d) (he : IsProIso f.e) : IsProIso f.c :=
  isProIso_of_mono_epi
    (f.isProMono ha.isProEpi hb.isProMono hd.isProMono)
    (f.isProEpi hb.isProEpi hd.isProEpi he.isProMono)

end FiveTermHom

end SerrePositivity.KST.ProExcision
