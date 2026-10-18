module

public import SerrePositivity.KST.DerivedBlowup.DGEndMonoid

/-!
概要：KST §3.1 の局所 dg 代数の一対象表示。
方針：複体のモノイド対象をその単位・積を持つ一対象 dg 圏へ戻す。
規約：基底環上の Hom 複体を直接使い、係数制限の対象移送を対象写像へ持ち込まない。
使われ方：同じ局所模型の表示を正規化して図式比較の型照合を簡潔にする。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory
open DifferentialGraded

variable {R : Type u} [CommRing R]

/-- 概要：指定した dg 代数を自己 Hom に持つ一対象の型。
方針：モノイド対象を添字として保持し、対象自体は一点とする。
規約：KST §3.1。使われ方：局所頂点の共通基底環上の正規表示。 -/
inductive AlgebraVertex (A : Mon (Complex R)) : Type u
  | point

/-- 概要：モノイド対象の単位・積から一対象 dg 圏を構成する。
方針：モノイドの左右単位律と結合律を dg 圏の unitor・associator の規約へ移す。
規約：KST §3.1。使われ方：局所 dg 代数を既存 DGCategory の型へ接続する。 -/
instance algebraVertexDGCategory (A : Mon (Complex R)) : DGCategory R (AlgebraVertex A) :=
  ofHomObjects R _ (fun _ _ => A.X) (fun _ => MonObj.one)
    (fun _ _ _ => MonObj.mul)
    (fun _ _ => by rw [MonObj.one_mul, Iso.inv_hom_id])
    (fun _ _ => by rw [MonObj.mul_one, Iso.inv_hom_id])
    (fun _ _ _ _ => by rw [MonObj.mul_assoc, Iso.inv_hom_id_assoc])

/-- 概要：自己 Hom の一対象表示から元の dg 圏への指定 dg 関手。
方針：対象を指定点へ送り、全 Hom 上では恒等鎖写像を使う。
規約：KST §3.1。使われ方：正規表示と元の局所 Koszul 模型の比較。 -/
def algebraVertexToOriginal (D : Type v) [DGCategory R D] (x : D) :
    DGFunctor R (AlgebraVertex (dgEndMonoid R D x)) D where
  obj _ := x
  map _ _ := 𝟙 _
  map_id _ := by simp; rfl
  map_comp _ _ _ := by simp; rfl

/-- 概要：一対象表示から元の指定点への比較は Hom 複体で同型。
方針：Hom 写像が恒等であることを使う。
規約：KST §3.1。使われ方：局所模型を正規表示で置き換える際の比較。 -/
instance algebraVertexToOriginalMapIsIso (D : Type v) [DGCategory R D] (x : D)
    (i j : AlgebraVertex (dgEndMonoid R D x)) :
    IsIso ((algebraVertexToOriginal D x).map i j) := by
  change IsIso (𝟙 _)
  infer_instance

end SerrePositivity.KST.DerivedBlowup
