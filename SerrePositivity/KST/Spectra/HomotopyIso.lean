module

public import SerrePositivity.KST.Spectra.HomotopyIsomorphism

/-!
概要：単体集合の同型が誘導するホモトピー類と群の同型。
方針：写像の関手性に同型の逆射の等式を適用する。
規約：基点の像の等式を明示する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5。loop の fiber 表示からの次数移動。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

variable {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]

omit [KanComplex X] [KanComplex Y] in
/-- 概要：単体集合の同型の逆射は指定基点を逆へ戻す。
方針：同型の合成の等式を頂点で評価する。
規約：h は順方向の基点の像。
使われ方：Kerodon §3.2.2。誘導写像の同型性。 -/
theorem iso_inverse_basepoint (e : X ≅ Y) {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (h : e.hom.app _ x = y) : e.inv.app _ y = x := by
  have hi := congrArg (fun k : X ⟶ X ↦ k.app _ x) e.hom_inv_id
  change e.inv.app _ (e.hom.app _ x) = x at hi
  rw [h] at hi
  exact hi

/-- 概要：単体集合の同型は全自然数次数のホモトピー類の同値を誘導する。
方針：逆射の誘導写像と恒等・合成の関手性を使う。
規約：零次数を含む。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5。fiber 表示の比較。 -/
noncomputable def KanHomotopy.equivOfIso (n : ℕ) (e : X ≅ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : e.hom.app _ x = y) :
    KanHomotopy X n x ≃ KanHomotopy Y n y := by
  let hi := iso_inverse_basepoint e h
  refine ⟨map n e.hom h, map n e.inv hi, ?_, ?_⟩
  · intro a
    have hc := congrArg (fun k : X ⟶ X ↦ k.app _ x) e.hom_inv_id
    have hm := map_comp n e.hom h e.inv hi hc a
    simpa only [e.hom_inv_id, map_id] using hm.symm
  · intro a
    have hc := congrArg (fun k : Y ⟶ Y ↦ k.app _ y) e.inv_hom_id
    have hm := map_comp n e.inv hi e.hom h hc a
    simpa only [e.inv_hom_id, map_id] using hm.symm

/-- 概要：単体集合の同型は正次数のホモトピー群の同型を誘導する。
方針：誘導準同型の全単射性を全次数の同値から得る。
規約：添字 n は実際の次数 n + 1 を表す。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5。loop の正次数の比較。 -/
noncomputable def KanHomotopyGroup.equivOfIso (n : ℕ) (e : X ≅ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : e.hom.app _ x = y) :
    KanHomotopyGroup X n x ≃* KanHomotopyGroup Y n y :=
  MulEquiv.ofBijective (map e.hom h) (KanHomotopy.equivOfIso (n + 1) e h).bijective

/-- 概要：全基点 π_* 同型の射は指定した正次数の群同型を誘導する。
方針：誘導準同型の全単射性を群同型へ束ねる。
規約：像の基点の等式を明示する。
使われ方：BF 1978 §2、HA §1.4.2。Ω 条件からの段の比較。 -/
noncomputable def KanHomotopyGroup.equivOfPiIsomorphism (n : ℕ) (f : X ⟶ Y)
    (hf : KanPiIsomorphism f) {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    KanHomotopyGroup X n x ≃* KanHomotopyGroup Y n y := by
  subst y
  exact MulEquiv.ofBijective (map f rfl) (hf x (n + 1))

end SerrePositivity.KST.Spectra
