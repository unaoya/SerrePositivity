module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.HomotopyIsomorphism

/-!
概要：単体集合の同型が誘導するホモトピー類と群の同型。
方針：写像の関手性に同型の逆射の等式を適用する。
規約：基点の像の等式を明示する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。loop の fiber 表示からの次数移動。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

variable {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]

/-- 概要：基点の等式によって誘導写像の全単射性を移す。
方針：二つの基点の等式で帰納する。
規約：両方の像の基点保存を明示する。
使われ方：Goerss–Jardine I §7。点つき置換から任意基点への移送。 -/
theorem KanHomotopy.map_bijective_congr (n : ℕ) (f : X ⟶ Y)
    {x x' : X _⦋0⦌} {y y' : Y _⦋0⦌} (hx : x = x') (hy : y = y')
    (h : f.app _ x = y) (h' : f.app _ x' = y')
    (hf : Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f h)) : Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f h') := by
  subst x'
  subst y'
  exact hf

omit [KanComplex X] [KanComplex Y] in
/-- 概要：単体集合の同型の逆射は指定基点を逆へ戻す。
方針：同型の合成の等式を頂点で評価する。
規約：h は順方向の基点の像。
使われ方：Kerodon §3.2.2（Tag 00VJ）。誘導写像の同型性。 -/
theorem iso_inverse_basepoint (e : X ≅ Y) {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (h : e.hom.app _ x = y) : e.inv.app _ y = x := by
  have hi := congrArg (fun k : X ⟶ X ↦ k.app _ x) e.hom_inv_id
  change e.inv.app _ (e.hom.app _ x) = x at hi
  rw [h] at hi
  exact hi

/-- 概要：単体集合の同型は全自然数次数のホモトピー類の同値を誘導する。
方針：逆射の誘導写像と恒等・合成の関手性を使う。
規約：零次数を含む。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。fiber 表示の比較。 -/
noncomputable def KanHomotopy.equivOfIso (n : ℕ) (e : X ≅ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : e.hom.app _ x = y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X n x ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy Y n y := by
  let hi := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.iso_inverse_basepoint e h
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n e.hom h, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n e.inv hi, ?_, ?_⟩
  · intro a
    have hc := congrArg (fun k : X ⟶ X ↦ k.app _ x) e.hom_inv_id
    have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_comp n e.hom h e.inv hi hc a
    simpa only [e.hom_inv_id, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_id] using hm.symm
  · intro a
    have hc := congrArg (fun k : Y ⟶ Y ↦ k.app _ y) e.inv_hom_id
    have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_comp n e.inv hi e.hom h hc a
    simpa only [e.inv_hom_id, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_id] using hm.symm

/-- 概要：単体集合の同型は正次数のホモトピー群の同型を誘導する。
方針：誘導準同型の全単射性を全次数の同値から得る。
規約：添字 n は実際の次数 n + 1 を表す。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。loop の正次数の比較。 -/
noncomputable def KanHomotopyGroup.equivOfIso (n : ℕ) (e : X ≅ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : e.hom.app _ x = y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x ≃* _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y n y :=
  MulEquiv.ofBijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map e.hom h) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfIso (n + 1) e h).bijective

/-- 概要：全基点 π_* 同型の射は指定した正次数の群同型を誘導する。
方針：誘導準同型の全単射性を群同型へ束ねる。
規約：像の基点の等式を明示する。
使われ方：BF 1978 §2、HA §1.4.2。Ω 条件からの段の比較。 -/
noncomputable def KanHomotopyGroup.equivOfPiIsomorphism (n : ℕ) (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f) {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x ≃* _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y n y := by
  subst y
  exact MulEquiv.ofBijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f rfl) (hf x (n + 1))

/-- 概要：全基点 π_* 同型による群同型の順写像は元の誘導準同型。
方針：像の基点の等式で帰納して全単射からの群同型を展開する。
規約：添字 n は実際の次数 n+1。
使われ方：Goerss–Jardine I §7、BF 1978 §2。段の比較の自然性。 -/
@[simp]
theorem KanHomotopyGroup.equivOfPiIsomorphism_apply (n : ℕ) (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f) {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism n f hf h a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f h a := by
  subst y
  rfl

/-- 概要：全基点 π_* 同型の射の指定基点の正次数の誘導準同型は全単射。
方針：像の基点の等式で帰納して元の全基点条件を使う。
規約：添字 n は実際の次数 n+1。
使われ方：Goerss–Jardine I §7。fiber 比較の五項補題。 -/
theorem KanHomotopyGroup.map_bijective_of_piIsomorphism (n : ℕ) (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f) {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) f h) := by
  subst y
  exact hf x (n + 1)

/-- 概要：全基点 π_* 同型の射は全自然数次数の類の同値を誘導する。
方針：指定基点への誘導写像の全単射性を同値へ束ねる。
規約：零次数を含む。
使われ方：BF 1978 §2、HA §1.4.2。Ω スペクトルの零段の比較。 -/
noncomputable def KanHomotopy.equivOfPiIsomorphism (n : ℕ) (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f) {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X n x ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy Y n y := by
  subst y
  exact Equiv.ofBijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f rfl) (hf x n)

/-- 概要：全基点 π_* 同型の同値の順写像は元の誘導写像。
方針：基点の等式で場合分けして全単射からの同値を展開する。
規約：零次数を含む。
使われ方：BF 1978 §2。置換射の全単射性の照合。 -/
@[simp]
theorem KanHomotopy.equivOfPiIsomorphism_apply (n : ℕ) (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f) {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X n x) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism n f hf h a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f h a := by
  subst y
  rfl

/-- 概要：単体集合の同型によるホモトピー類の同値は基点を保つ。
方針：誘導写像の基点保存を適用する。
規約：零次数を含む。
使われ方：Goerss–Jardine I §7。loop の連結成分の単位の照合。 -/
@[simp]
theorem KanHomotopy.equivOfIso_point (n : ℕ) (e : X ≅ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : e.hom.app _ x = y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfIso n e h (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_point n e.hom h

/-- 概要：全基点 π_* 同型による類の同値は基点を保つ。
方針：基点の像で場合分けして誘導写像の基点保存を使う。
規約：零次数を含む。
使われ方：BF 1978 §2。Ω スペクトルの零次数の単位。 -/
@[simp]
theorem KanHomotopy.equivOfPiIsomorphism_point (n : ℕ) (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f) {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism n f hf h (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n := by
  subst y
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_point n f rfl

/-- 概要：単体集合の同型の順射は全基点 π_* 同型。
方針：任意の源の基点で構成済みのホモトピー類の同値を使う。
規約：零次数も含む。
使われ方：Goerss–Jardine I §7、BF 1978 §2。loop と fiber の厳密同型の移送。 -/
theorem KanPiIsomorphism.of_iso (e : X ≅ Y) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism e.hom := by
  intro x n
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfIso n e rfl).bijective

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism export _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism (of_iso)


end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.iso_inverse_basepoint := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.iso_inverse_basepoint

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopy.equivOfIso := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopy.equivOfIso_point := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfIso_point

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopy.equivOfPiIsomorphism := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopy.equivOfPiIsomorphism_apply := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism_apply

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopy.equivOfPiIsomorphism_point := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism_point

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopy.map_bijective_congr := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_bijective_congr

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.equivOfIso := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.equivOfPiIsomorphism := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.equivOfPiIsomorphism_apply := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism_apply

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.map_bijective_of_piIsomorphism := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_bijective_of_piIsomorphism

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanPiIsomorphism.of_iso := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopy.equivOfIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopy.equivOfIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.equivOfIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.equivOfIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.equivOfPiIsomorphism._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.equivOfPiIsomorphism._proof_2 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.equivOfPiIsomorphism._proof_3 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism._proof_3
