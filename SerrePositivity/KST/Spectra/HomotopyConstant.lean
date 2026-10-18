module

public import SerrePositivity.KST.Spectra.HomotopyZeroRelations

/-!
概要：定数射がホモトピー類に誘導する写像。
方針：代表単体の後合成が定数単体となることを使う。
規約：零次数を含む全自然数次数。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5。収縮する全空間のホモトピー群。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.KanHomotopy

/-- 概要：定数射は全てのホモトピー類を基点へ送る。
方針：代表単体を取り、定数射との合成を計算する。
規約：基点の像の証明は任意。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5。path space の収縮。 -/
theorem map_const {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (n : ℕ) {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (hc : (SSet.const (X := X) y).app _ x = y) (a : KanHomotopy X n x) :
    map n (SSet.const y) hc a = point n := by
  obtain ⟨s, rfl⟩ := mk_surjective n a
  rw [map_mk]
  have hs : mapSimplex (SSet.const y) hc s = .const := by
    ext : 1
    exact SSet.comp_const _ _
  rw [hs, mk_const]

end SerrePositivity.KST.Spectra.KanHomotopy
