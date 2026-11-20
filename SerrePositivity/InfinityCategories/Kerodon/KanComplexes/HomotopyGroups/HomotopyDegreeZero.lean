module


public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyGroups
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：境界定数単体による零次数のホモトピー類と連結成分との比較。
方針：零単体の RelStruct は逆向きの辺であり、その商を Mathlib の π₀ と同定する。
規約：零次数には一般の群構造を付けない。Kan 性なしでも比較は成立する。
使われ方：Kerodon Example 3.2.2.6（Tag 00VQ）、Goerss–Jardine I §7。長完全列の端点。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Spectra.KanHomotopyZero
end SerrePositivity.KST.Spectra.KanHomotopyZero
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

/-- 概要：零次数の境界定数単体のホモトピー類。
方針：RelStruct₀ による辺の関係を商にする。
規約：零次数の境界は空であり、基点は代表を制限しない。
使われ方：Kerodon Example 3.2.2.6（Tag 00VQ）。π₀ との比較。 -/
@[kerodon 00HC, kerodon 00VQ]
def KanHomotopyZero (X : SSet.{u}) (x : X _⦋0⦌) : Type u :=
  Quot (fun f g : X.PtSimplex 0 x ↦ Nonempty (PtSimplex.RelStruct₀ f g))

namespace KanHomotopyZero


variable {X : SSet.{u}} {x : X _⦋0⦌}

/-- 概要：零単体のホモトピー類。
方針：関係の商への標準射。
規約：単体の境界は空。
使われ方：Kerodon Example 3.2.2.6（Tag 00VQ）。零次数の代表計算。 -/
def mk (f : X.PtSimplex 0 x) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero X x := Quot.mk _ f

/-- 概要：零次数のホモトピー類と連結成分の標準的な全単射。
方針：RelStruct₀ と辺の同値で商の間の互いに逆な写像を作る。
規約：辺の向きが逆なので商の等式の対称性を使う。
使われ方：Kerodon Example 3.2.2.6（Tag 00VQ）。fiber 長完全列の π₀。 -/
@[kerodon 00HC, kerodon 00VQ]
def equivPiZero : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero X x ≃ π₀ X where
  toFun := Quot.lift (fun f ↦ π₀.mk (PtSimplex.equiv₀ x f)) (by
    rintro f g ⟨h⟩
    exact (π₀.sound (PtSimplex.RelStruct₀.equiv₀ h)).symm)
  invFun := π₀.lift (fun v ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.mk ((PtSimplex.equiv₀ x).symm v)) (by
    intro v w e
    exact (Quot.sound ⟨PtSimplex.RelStruct₀.equiv₀.symm
      (by simpa only [Equiv.apply_symm_apply] using e)⟩).symm)
  left_inv a := by
    induction a using Quot.inductionOn with | h f => ?_
    exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.mk ((PtSimplex.equiv₀ x).symm_apply_apply f)
  right_inv a := by
    induction a using π₀.rec with | mk v => ?_
    exact congrArg π₀.mk ((PtSimplex.equiv₀ x).apply_symm_apply v)

/-- 概要：零次数の代表の比較像は対応する頂点の連結成分。
方針：商からの写像の定義を計算する。
規約：基点に依存しない連結成分を得る。
使われ方：Kerodon Example 3.2.2.6（Tag 00VQ）。比較写像の自然性。 -/
@[simp]
theorem equivPiZero_mk (f : X.PtSimplex 0 x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.mk f) = π₀.mk (PtSimplex.equiv₀ x f) := rfl

/-- 概要：基点を保つ射による零次数の誘導写像。
方針：代表と RelStruct₀ を後合成して商へ降ろす。
規約：Kan 性は不要。
使われ方：Kerodon §3.2.2（Tag 00VJ）。長完全列の端の自然性。 -/
def map {Y : SSet.{u}} {y : Y _⦋0⦌} (φ : X ⟶ Y) (hφ : φ.app _ x = y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero X x → _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero Y y :=
  Quot.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex φ hφ) (fun _ _ ⟨r⟩ ↦ ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapRelStruct φ hφ r⟩)

/-- 概要：零次数の誘導写像の代表上の計算。
方針：商への写像の定義による。
規約：基点の像を hφ で指定する。
使われ方：Kerodon §3.2.2（Tag 00VJ）。関手性と比較。 -/
@[simp]
theorem map_mk {Y : SSet.{u}} {y : Y _⦋0⦌} (φ : X ⟶ Y)
    (hφ : φ.app _ x = y) (f : X.PtSimplex 0 x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.map φ hφ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.mk f) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex φ hφ f) := rfl

/-- 概要：π₀ との比較は単体集合の射について自然。
方針：零単体に対する後合成を Yoneda で計算する。
規約：基点の像を指定した任意の射。
使われ方：Kerodon Example 3.2.2.6（Tag 00VQ）。零次数の標準界面。 -/
@[simp]
theorem equivPiZero_map {Y : SSet.{u}} {y : Y _⦋0⦌} (φ : X ⟶ Y)
    (hφ : φ.app _ x = y) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero X x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.map φ hφ a) = mapπ₀ φ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero a) := by
  induction a using Quot.inductionOn with | h f => rfl

/-- 概要：零次数の誘導写像は恒等射を保つ。
方針：代表の後合成を計算する。
規約：基点は同じ。
使われ方：Kerodon §3.2.2（Tag 00VJ）。零次数の関手性。 -/
@[simp]
theorem map_id (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero X x) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.map (𝟙 X) rfl a = a := by
  induction a using Quot.inductionOn with | h f => ?_
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (𝟙 X) rfl f) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.mk f
  congr 1

/-- 概要：零次数の誘導写像は合成を保つ。
方針：代表単体の後合成の結合則を使う。
規約：基点の像は各射と合成射について指定する。
使われ方：Kerodon §3.2.2（Tag 00VJ）。零次数の関手性。 -/
theorem map_comp {Y Z : SSet.{u}} {y : Y _⦋0⦌} {z : Z _⦋0⦌}
    (φ : X ⟶ Y) (hφ : φ.app _ x = y) (ψ : Y ⟶ Z) (hψ : ψ.app _ y = z)
    (hcomp : (φ ≫ ψ).app _ x = z) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero X x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.map (φ ≫ ψ) hcomp a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.map ψ hψ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.map φ hφ a) := by
  induction a using Quot.inductionOn with | h f => ?_
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (φ ≫ ψ) hcomp f) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex ψ hψ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex φ hφ f))
  congr 1

end KanHomotopyZero

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
