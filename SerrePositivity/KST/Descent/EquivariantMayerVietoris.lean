module

public import SerrePositivity.KST.Descent.MayerVietoris
public import SerrePositivity.KST.Descent.InvariantExactness

/-!
# G 同変な全次数長完全列と有理不変部分

## 概要
境界を含めて G 同変な Mayer–Vietoris 列に不変部分を適用し、全次数で完全な列を得る。

## 方針
各次数の実際の表現と、制限・差・境界の同変性を保持する。
平均による完全性保存を三つの隣接二射に適用し、列の比較も不変部分へ制限する。

## 規約
通常の有理不変部分についての構成。π_n(hG) との同定は L9 の実構成との接続で必要。
加群の有限次元性や次数の有界性を要求しない。

## 使われ方
論文 定理 3.1 の G 同変な軌道正方形と (3.8) に対する帰納の π_* 側。
-/

@[expose] public section

universe u

open Representation

namespace SerrePositivity.KST.Descent.GradedMayerVietoris

variable {G : Type*} [Group G]

/-- 概要：長完全列の境界まで保つ G 作用（論文 定理 3.1 の軌道正方形）。
方針：三種類の項の表現と、三つの写像の同変性を保持する。
規約：境界の同変性を各項の作用だけから推論しない。
使われ方：有限群の有理不変部分で全次数の完全列を作る。 -/
structure Action (S : GradedMayerVietoris.{u}) (G : Type*) [Group G] where
  /-- 概要：A の各次数の表現（論文 §3）。
  方針：実際の有理表現を保持する。
  規約：係数上の作用もこの表現に含む。
  使われ方：元のスキームの固定部分。 -/
  ρA : ∀ n, Representation ℚ G (S.A n)
  /-- 概要：B の各次数の表現（論文 §3）。
  方針：実際の有理表現を保持する。
  規約：部分の積への作用との同定は具体的な正方形で行う。
  使われ方：(3.8) の置換作用。 -/
  ρB : ∀ n, Representation ℚ G (S.B n)
  /-- 概要：C の各次数の表現（論文 §3）。
  方針：実際の有理表現を保持する。
  規約：境界の始域にも同じ G が作用する。
  使われ方：中心上の固定部分。 -/
  ρC : ∀ n, Representation ℚ G (S.C n)
  /-- 概要：制限の同変性（論文 §3）。
  方針：与えた制限線形写像に対して表現との両立を要求する。
  規約：写像を別の同型へ取り替えない。
  使われ方：不変部分への値域制限。 -/
  restriction_equivariant : ∀ n, IsIntertwiningMap (ρA n) (ρB n) (S.restriction n)
  /-- 概要：制限の差の同変性（論文 §3）。
  方針：符号を含む指定線形写像に同変性を要求する。
  規約：全整数次数を含む。
  使われ方：不変部分の列の第二の射。 -/
  difference_equivariant : ∀ n, IsIntertwiningMap (ρB n) (ρC n) (S.difference n)
  /-- 概要：境界写像の同変性（論文 §3）。
  方針：次数 n+1 と n の作用の両立を保持する。
  規約：長完全列の自然性から供給すべきデータ。
  使われ方：不変部分の列の境界と完全性。 -/
  boundary_equivariant : ∀ n, IsIntertwiningMap (ρC (n + 1)) (ρA n) (S.boundary n)

variable {S T : GradedMayerVietoris.{u}}

/-- 概要：同変な制限を bundled な表現の射へ移す（論文 §3）。
方針：同じ線形写像にその同変性の証明を付ける。
規約：値は元の指定制限と同じ。
使われ方：有理不変部分の制限射。 -/
def Action.restrictionMap (a : Action S G) (n : ℤ) : IntertwiningMap (a.ρA n) (a.ρB n) :=
  (S.restriction n).intertwiningMap_of_isIntertwiningMap _ _
    (a.restriction_equivariant n).isIntertwining

/-- 概要：同変な制限の差を表現の射へ移す（論文 §3）。
方針：同じ線形写像に同変性の証明を付ける。
規約：符号を変えない。
使われ方：有理不変部分の列の第二の射。 -/
def Action.differenceMap (a : Action S G) (n : ℤ) : IntertwiningMap (a.ρB n) (a.ρC n) :=
  (S.difference n).intertwiningMap_of_isIntertwiningMap _ _
    (a.difference_equivariant n).isIntertwining

/-- 概要：同変な境界を表現の射へ移す（論文 §3）。
方針：指定した境界にその同変性の証明を付ける。
規約：次数 n+1 から n への写像のまま。
使われ方：有理不変部分の境界と完全性。 -/
def Action.boundaryMap (a : Action S G) (n : ℤ) : IntertwiningMap (a.ρC (n + 1)) (a.ρA n) :=
  (S.boundary n).intertwiningMap_of_isIntertwiningMap _ _
    (a.boundary_equivariant n).isIntertwining

/-- 概要：有限群の有理不変部分を取った列も全次数で完全（論文 定理 3.1、(3.8)）。
方針：平均による完全性保存を三箇所の隣接二射へ適用する。
規約：非有界な整数次数の列をそのまま扱い、スペクトル系列の収束は使わない。
使われ方：軌道正方形で hG の π_* と通常の不変部分を同定した後の比較。 -/
noncomputable def Action.fixedSequence [Finite G] (a : Action S G) : GradedMayerVietoris.{u} where
  A n := ModuleCat.of ℚ (a.ρA n).invariants
  B n := ModuleCat.of ℚ (a.ρB n).invariants
  C n := ModuleCat.of ℚ (a.ρC n).invariants
  restriction n := invariantMap (a.restrictionMap n)
  difference n := invariantMap (a.differenceMap n)
  boundary n := invariantMap (a.boundaryMap n)
  exact_boundary_restriction n := invariantMap_exact (a.boundaryMap n) (a.restrictionMap n)
    (S.exact_boundary_restriction n)
  exact_restriction_difference n := invariantMap_exact (a.restrictionMap n) (a.differenceMap n)
    (S.exact_restriction_difference n)
  exact_difference_boundary n := invariantMap_exact (a.differenceMap (n + 1)) (a.boundaryMap n)
    (S.exact_difference_boundary n)

/-- 概要：長完全列の比較が三種類の G 作用と両立するというデータ（論文 §3）。
方針：各指定比較に同変性を付ける。
規約：制限・差・境界との可換性は元の `Hom` が保持する。
使われ方：比較を有理不変部分の列へ移す。 -/
structure EquivariantHom (f : Hom S T) (source : Action S G) (target : Action T G) where
  /-- 概要：A の指定比較の同変性（論文 §3）。
  方針：元の比較線形写像に対して要求する。
  規約：同型性の仮定ではない。
  使われ方：固定部分の比較の結論。 -/
  mapA_equivariant : ∀ n, IsIntertwiningMap (source.ρA n) (target.ρA n) (f.mapA n)
  /-- 概要：B の指定比較の同変性（論文 §3）。
  方針：元の比較線形写像に対して要求する。
  規約：同型性は別の定理の仮定。
  使われ方：固定部分の比較の既知の辺。 -/
  mapB_equivariant : ∀ n, IsIntertwiningMap (source.ρB n) (target.ρB n) (f.mapB n)
  /-- 概要：C の指定比較の同変性（論文 §3）。
  方針：元の比較線形写像に対して要求する。
  規約：次数を切り捨てない。
  使われ方：中心上の帰納仮定。 -/
  mapC_equivariant : ∀ n, IsIntertwiningMap (source.ρC n) (target.ρC n) (f.mapC n)

variable {f : Hom S T} {source : Action S G} {target : Action T G}

/-- 概要：比較の A 成分を同変写像として保持する（論文 §3）。
方針：同じ線形写像に同変性を付ける。
規約：指定比較を変更しない。
使われ方：固定部分の比較の A 成分。 -/
def EquivariantHom.mapAIntertwining (e : EquivariantHom f source target) (n : ℤ) :
    IntertwiningMap (source.ρA n) (target.ρA n) :=
  (f.mapA n).intertwiningMap_of_isIntertwiningMap _ _ (e.mapA_equivariant n).isIntertwining

/-- 概要：比較の B 成分を同変写像として保持する（論文 §3）。
方針：同じ線形写像に同変性を付ける。
規約：指定比較を変更しない。
使われ方：(3.8) による固定部分の比較。 -/
def EquivariantHom.mapBIntertwining (e : EquivariantHom f source target) (n : ℤ) :
    IntertwiningMap (source.ρB n) (target.ρB n) :=
  (f.mapB n).intertwiningMap_of_isIntertwiningMap _ _ (e.mapB_equivariant n).isIntertwining

/-- 概要：比較の C 成分を同変写像として保持する（論文 §3）。
方針：同じ線形写像に同変性を付ける。
規約：指定比較を変更しない。
使われ方：中心上の固定部分の比較。 -/
def EquivariantHom.mapCIntertwining (e : EquivariantHom f source target) (n : ℤ) :
    IntertwiningMap (source.ρC n) (target.ρC n) :=
  (f.mapC n).intertwiningMap_of_isIntertwiningMap _ _ (e.mapC_equivariant n).isIntertwining

/-- 概要：同変な長完全列の比較を固定部分の長完全列の比較へ制限（論文 定理 3.1）。
方針：三項の比較を不変部分に制限し、元の三つの可換式を元で評価する。
規約：境界の自然性も保持する。
使われ方：(3.8) と中心上の帰納仮定を五項補題に接続する。 -/
noncomputable def EquivariantHom.fixedHom [Finite G] (e : EquivariantHom f source target) :
    Hom source.fixedSequence target.fixedSequence where
  mapA n := invariantMap (e.mapAIntertwining n)
  mapB n := invariantMap (e.mapBIntertwining n)
  mapC n := invariantMap (e.mapCIntertwining n)
  comm_restriction n := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (f.comm_restriction n) x.val
  comm_difference n := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (f.comm_difference n) x.val
  comm_boundary n := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (f.comm_boundary n) x.val

/-- 概要：B と C の固定部分の比較が全次数同型なら A の固定部分の比較も同型（定理 3.1）。
方針：不変部分で完全な列と境界に自然な比較を作り、全次数の五項補題を使う。
規約：B と C 自体の比較の同型性は不要で、不変部分の比較だけを仮定する。
使われ方：置換作用の (3.8) と中心上の帰納仮定から軌道正方形を閉じる。 -/
theorem EquivariantHom.bijective_fixed_mapA [Finite G] (e : EquivariantHom f source target)
    (hB : ∀ n, Function.Bijective (invariantMap (e.mapBIntertwining n)))
    (hC : ∀ n, Function.Bijective (invariantMap (e.mapCIntertwining n))) (n : ℤ) :
    Function.Bijective (invariantMap (e.mapAIntertwining n)) :=
  e.fixedHom.bijective_mapA hB hC n

end SerrePositivity.KST.Descent.GradedMayerVietoris
