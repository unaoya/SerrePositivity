module

public import SerrePositivity.KST.Spectra.HomotopyGroups
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-!
概要：境界定数単体による零次数のホモトピー類と連結成分との比較。
方針：零単体の RelStruct は逆向きの辺であり、その商を Mathlib の π₀ と同定する。
規約：零次数には一般の群構造を付けない。Kan 性なしでも比較は成立する。
使われ方：Kerodon Example 3.2.2.6、Goerss–Jardine I §7。長完全列の端点。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

/-- 概要：零次数の境界定数単体のホモトピー類。
方針：RelStruct₀ による辺の関係を商にする。
規約：零次数の境界は空であり、基点は代表を制限しない。
使われ方：Kerodon Example 3.2.2.6。π₀ との比較。 -/
def KanHomotopyZero (X : SSet.{u}) (x : X _⦋0⦌) : Type u :=
  Quot (fun f g : X.PtSimplex 0 x ↦ Nonempty (PtSimplex.RelStruct₀ f g))

namespace KanHomotopyZero

variable {X : SSet.{u}} {x : X _⦋0⦌}

/-- 概要：零単体のホモトピー類。
方針：関係の商への標準射。
規約：単体の境界は空。
使われ方：Kerodon Example 3.2.2.6。零次数の代表計算。 -/
def mk (f : X.PtSimplex 0 x) : KanHomotopyZero X x := Quot.mk _ f

/-- 概要：零次数のホモトピー類と連結成分の標準的な全単射。
方針：RelStruct₀ と辺の同値で商の間の互いに逆な写像を作る。
規約：辺の向きが逆なので商の等式の対称性を使う。
使われ方：Kerodon Example 3.2.2.6。fiber 長完全列の π₀。 -/
def equivPiZero : KanHomotopyZero X x ≃ π₀ X where
  toFun := Quot.lift (fun f ↦ π₀.mk (PtSimplex.equiv₀ x f)) (by
    rintro f g ⟨h⟩
    exact (π₀.sound (PtSimplex.RelStruct₀.equiv₀ h)).symm)
  invFun := π₀.lift (fun v ↦ mk ((PtSimplex.equiv₀ x).symm v)) (by
    intro v w e
    exact (Quot.sound ⟨PtSimplex.RelStruct₀.equiv₀.symm
      (by simpa only [Equiv.apply_symm_apply] using e)⟩).symm)
  left_inv a := by
    induction a using Quot.inductionOn with | h f => ?_
    exact congrArg mk ((PtSimplex.equiv₀ x).symm_apply_apply f)
  right_inv a := by
    induction a using π₀.rec with | mk v => ?_
    exact congrArg π₀.mk ((PtSimplex.equiv₀ x).apply_symm_apply v)

/-- 概要：零次数の代表の比較像は対応する頂点の連結成分。
方針：商からの写像の定義を計算する。
規約：基点に依存しない連結成分を得る。
使われ方：Kerodon Example 3.2.2.6。比較写像の自然性。 -/
@[simp]
theorem equivPiZero_mk (f : X.PtSimplex 0 x) :
    equivPiZero (mk f) = π₀.mk (PtSimplex.equiv₀ x f) := rfl

/-- 概要：基点を保つ射による零次数の誘導写像。
方針：代表と RelStruct₀ を後合成して商へ降ろす。
規約：Kan 性は不要。
使われ方：Kerodon §3.2.2。長完全列の端の自然性。 -/
def map {Y : SSet.{u}} {y : Y _⦋0⦌} (φ : X ⟶ Y) (hφ : φ.app _ x = y) :
    KanHomotopyZero X x → KanHomotopyZero Y y :=
  Quot.map (mapSimplex φ hφ) (fun _ _ ⟨r⟩ ↦ ⟨mapRelStruct φ hφ r⟩)

/-- 概要：零次数の誘導写像の代表上の計算。
方針：商への写像の定義による。
規約：基点の像を hφ で指定する。
使われ方：Kerodon §3.2.2。関手性と比較。 -/
@[simp]
theorem map_mk {Y : SSet.{u}} {y : Y _⦋0⦌} (φ : X ⟶ Y)
    (hφ : φ.app _ x = y) (f : X.PtSimplex 0 x) :
    map φ hφ (mk f) = mk (mapSimplex φ hφ f) := rfl

/-- 概要：π₀ との比較は単体集合の射について自然。
方針：零単体に対する後合成を Yoneda で計算する。
規約：基点の像を指定した任意の射。
使われ方：Kerodon Example 3.2.2.6。零次数の標準界面。 -/
@[simp]
theorem equivPiZero_map {Y : SSet.{u}} {y : Y _⦋0⦌} (φ : X ⟶ Y)
    (hφ : φ.app _ x = y) (a : KanHomotopyZero X x) :
    equivPiZero (map φ hφ a) = mapπ₀ φ (equivPiZero a) := by
  induction a using Quot.inductionOn with | h f => rfl

/-- 概要：零次数の誘導写像は恒等射を保つ。
方針：代表の後合成を計算する。
規約：基点は同じ。
使われ方：Kerodon §3.2.2。零次数の関手性。 -/
@[simp]
theorem map_id (a : KanHomotopyZero X x) : map (𝟙 X) rfl a = a := by
  induction a using Quot.inductionOn with | h f => ?_
  change mk (mapSimplex (𝟙 X) rfl f) = mk f
  congr 1

/-- 概要：零次数の誘導写像は合成を保つ。
方針：代表単体の後合成の結合則を使う。
規約：基点の像は各射と合成射について指定する。
使われ方：Kerodon §3.2.2。零次数の関手性。 -/
theorem map_comp {Y Z : SSet.{u}} {y : Y _⦋0⦌} {z : Z _⦋0⦌}
    (φ : X ⟶ Y) (hφ : φ.app _ x = y) (ψ : Y ⟶ Z) (hψ : ψ.app _ y = z)
    (hcomp : (φ ≫ ψ).app _ x = z) (a : KanHomotopyZero X x) :
    map (φ ≫ ψ) hcomp a = map ψ hψ (map φ hφ a) := by
  induction a using Quot.inductionOn with | h f => ?_
  change mk (mapSimplex (φ ≫ ψ) hcomp f) =
    mk (mapSimplex ψ hψ (mapSimplex φ hφ f))
  congr 1

end KanHomotopyZero

end SerrePositivity.KST.Spectra
