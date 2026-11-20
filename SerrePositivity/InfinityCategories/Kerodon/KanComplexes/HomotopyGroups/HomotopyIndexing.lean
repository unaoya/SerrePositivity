module


public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyInvariance
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.Commutativity

/-!
概要：実際の自然数次数で添字付けした Kan 複体のホモトピー類。
方針：零次数の商と正次数の群を次数でまとめる。
規約：KanHomotopy X n x の n は実際の次数。零次数は基点付き集合。
使われ方：Kerodon §3.2.2（Tag 00VJ）、Goerss–Jardine I §7。長完全列の全次数の界面。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Spectra.KanHomotopy
end SerrePositivity.KST.Spectra.KanHomotopy
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

/-- 概要：Kan 複体の自然数次数のホモトピー類。
方針：零次数は RelStruct₀ の商、正次数は充填関係による群とする。
規約：n は実際の次数であり、零次数に群構造を要求しない。
使われ方：Kerodon Construction 3.2.2.4（Tag 00VN）、Example 3.2.2.6（Tag 00VQ）、Theorem 3.2.2.10（Tag 00VU）。 -/
def KanHomotopy (X : SSet.{u}) [KanComplex X] (n : ℕ) (x : X _⦋0⦌) : Type u :=
  match n with
  | 0 => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero X x
  | n + 1 => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x

namespace KanHomotopy


variable {X Y Z : SSet.{u}} [KanComplex X] [KanComplex Y] [KanComplex Z]
  {x : X _⦋0⦌} {y : Y _⦋0⦌} {z : Z _⦋0⦌}

/-- 概要：任意の自然数次数の境界定数単体のホモトピー類。
方針：零次数と正次数の商への標準射をまとめる。
規約：n は代表単体の実際の次数。
使われ方：Kerodon Construction 3.2.2.4（Tag 00VN）。連結射の全次数の定義。 -/
def mk (n : ℕ) (s : X.PtSimplex n x) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X n x :=
  match n with
  | 0 => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.mk s
  | _ + 1 => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s

/-- 概要：任意の面添字の RelStruct は全自然数次数の類の等式を与える。
方針：零次数では辺の商、正次数では面添字独立性を使う。
規約：零次数の面添字は唯一の零。
使われ方：Kerodon §3.2.2（Tag 00VJ）。連結写像の選択独立性。 -/
theorem sound {n : ℕ} {s t : X.PtSimplex n x} {i : Fin (n + 1)}
    (r : PtSimplex.RelStruct s t i) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n s = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n t := by
  cases n with
  | zero =>
    have hi : i = 0 := by apply Fin.ext; omega
    subst i
    exact Quot.sound ⟨r⟩
  | succ n => exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.sound r

/-- 概要：正の自然数次数のホモトピー類には群構造がある。
方針：充填で構成済みの正次数の群構造を使う。
規約：実際の次数 n + 1。
使われ方：Kerodon Theorem 3.2.2.10（Tag 00VU）。長完全列の群の部分。 -/
noncomputable instance instGroupHAddNatOfNat {n : ℕ} : Group (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X (n + 1) x) :=
  inferInstanceAs (Group (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x))

/-- 概要：二以上の自然数次数のホモトピー類には可換群構造がある。
方針：四面の比較で構成済みの可換群構造を使う。
規約：実際の次数 n + 2。
使われ方：Kerodon Theorem 3.2.2.10（Tag 00VU）。スペクトルへの安定化。 -/
noncomputable instance instCommGroupHAddNatOfNat {n : ℕ} : CommGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X (n + 2) x) :=
  inferInstanceAs (CommGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X (n + 1) x))

/-- 概要：全ての自然数次数のホモトピー類の基点。
方針：零次数では x の連結成分、正次数では定数単体の類を取る。
規約：群のある次数では単位元と一致する。
使われ方：Kerodon §3.2.2（Tag 00VJ）。長完全列の基点付き集合の端。 -/
def point (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X n x :=
  match n with
  | 0 => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.mk ((PtSimplex.equiv₀ x).symm x)
  | _ + 1 => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk .const

/-- 概要：定数単体の類は全次数で基点となる。
方針：零次数では Yoneda による頂点の表示、正次数では単位元の定義を使う。
規約：n は実際の次数。
使われ方：Kerodon §3.2.2（Tag 00VJ）。連結写像の基点保存。 -/
@[simp]
theorem mk_const (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n (RelativeMorphism.const : X.PtSimplex n x) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n := by
  cases n with
  | zero =>
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.mk .const = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.mk ((PtSimplex.equiv₀ x).symm x)
    congr 1
    ext : 1
    exact (yonedaEquiv_symm_zero x).symm
  | succ n => rfl

/-- 概要：全自然数次数のホモトピー類の誘導写像。
方針：零次数と正次数の構成済みの誘導写像をまとめる。
規約：基点の像を hφ で指定する。
使われ方：Kerodon §3.2.2（Tag 00VJ）。π_* 同型を述べる共通界面。 -/
noncomputable def map (n : ℕ) (φ : X ⟶ Y) (hφ : φ.app _ x = y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X n x → _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy Y n y :=
  match n with
  | 0 => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.map φ hφ
  | _ + 1 => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map φ hφ

/-- 概要：全次数の誘導写像を代表単体上で計算する。
方針：次数による場合分けで商への写像の定義を読む。
規約：像の基点は hφ により指定する。
使われ方：Kerodon §3.2.2（Tag 00VJ）。連結写像と fiber 列の計算。 -/
@[simp]
theorem map_mk (n : ℕ) (φ : X ⟶ Y) (hφ : φ.app _ x = y) (s : X.PtSimplex n x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n φ hφ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n s) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex φ hφ s) := by
  cases n <;> rfl

/-- 概要：全次数の誘導写像は恒等射を保つ。
方針：零次数と正次数それぞれの恒等法則を使う。
規約：基点は同じ x。
使われ方：Kerodon §3.2.2（Tag 00VJ）。全次数の関手性。 -/
@[simp]
theorem map_id (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X n x) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (𝟙 X) rfl a = a := by
  cases n with
  | zero => exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.map_id a
  | succ n => exact DFunLike.congr_fun _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_id a

/-- 概要：全次数の誘導写像は合成を保つ。
方針：零次数と正次数それぞれの合成法則を使う。
規約：hcomp は合成射の基点保存を指定する。
使われ方：Kerodon §3.2.2（Tag 00VJ）。全次数の自然性。 -/
theorem map_comp (n : ℕ) (φ : X ⟶ Y) (hφ : φ.app _ x = y)
    (ψ : Y ⟶ Z) (hψ : ψ.app _ y = z) (hcomp : (φ ≫ ψ).app _ x = z)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X n x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (φ ≫ ψ) hcomp a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n ψ hψ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n φ hφ a) := by
  cases n with
  | zero => exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.map_comp φ hφ ψ hψ hcomp a
  | succ n => exact DFunLike.congr_fun (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp φ hφ ψ hψ hcomp) a

/-- 概要：全次数の誘導写像はホモトピー類の基点を保つ。
方針：零次数では基点の像、正次数では群準同型の単位保存を使う。
規約：hφ により指定した y を標的の基点とする。
使われ方：Kerodon §3.2.2（Tag 00VJ）。基点付き長完全列の界面。 -/
@[simp]
theorem map_point (n : ℕ) (φ : X ⟶ Y) (hφ : φ.app _ x = y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n φ hφ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n := by
  cases n with
  | zero =>
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero.injective
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero_map,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero_mk, mapπ₀_mk, Equiv.apply_symm_apply, hφ]
  | succ n => exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map φ hφ).map_one

/-- 概要：基点固定ホモトピーの両端の誘導写像は全自然数次数で一致する。
方針：正次数の prism の計算と零次数の辺の計算をまとめる。
規約：ホモトピーは基点上に定数。
使われ方：Kerodon Proposition 3.2.1.4（Tag 00V9） と §3.2.2。全次数のホモトピー不変性。 -/
theorem map_eq_of_basedHomotopy (n : ℕ) {φ ψ : X ⟶ Y}
    (hφ : φ.app _ x = y) (hψ : ψ.app _ x = y)
    (H : (RelativeMorphism.ofSimplex₀ φ x y hφ).Homotopy
      (RelativeMorphism.ofSimplex₀ ψ x y hψ)) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X n x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n φ hφ a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n ψ hψ a := by
  cases n with
  | zero =>
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.map_eq_of_homotopy hφ hψ ?_ a
    exact { h := H.h, h₀ := H.h₀, h₁ := H.h₁
            rel := by ext m ⟨⟨v, hv⟩, t⟩; exact hv.elim }
  | succ n =>
    exact DFunLike.congr_fun (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_eq_of_basedHomotopy hφ hψ H) a

end KanHomotopy

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
