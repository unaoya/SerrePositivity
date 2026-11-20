module


public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.HomotopyZeroRelations

/-!
概要：定数射がホモトピー類に誘導する写像。
方針：代表単体の後合成が定数単体となることを使う。
規約：零次数を含む全自然数次数。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。収縮する全空間のホモトピー群。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.KanHomotopy
end SerrePositivity.KST.Spectra.KanHomotopy
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups


/-- 概要：定数射は全てのホモトピー類を基点へ送る。
方針：代表単体を取り、定数射との合成を計算する。
規約：基点の像の証明は任意。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。path space の収縮。 -/
theorem map_const {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (n : ℕ) {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (hc : (SSet.const (X := X) y).app _ x = y) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X n x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (SSet.const y) hc a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n := by
  obtain ⟨s, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_surjective n a
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_mk]
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (SSet.const y) hc s = .const := by
    ext : 1
    exact SSet.comp_const _ _
  rw [hs, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk_const]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy export _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups (map_const)


end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
