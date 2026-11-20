module


public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIso

/-!
概要：自己射の二回合成から全基点の π_* 同型性を検出する。
方針：基点 x とその像 f(x) での二つの合成の全単射性を使う。
規約：基点を移す射にも適用できる。
使われ方：Goerss–Jardine I §7、BF 1978 §2。loop の符号反転の全基点での比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：自己射の二回合成が全基点の π_* 同型なら元の自己射もそうである。
方針：隣接する二つの基点で合成の全単射性を使い、単射性と全射性を検査する。
規約：全自然数次数と全ての基点を扱う。
使われ方：Goerss–Jardine I §7、BF 1978 §2。ホモトピー対合の π_* 同型性。 -/
theorem KanPiIsomorphism.of_self_comp {X : SSet.{u}} [KanComplex X] (f : X ⟶ X)
    (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f ≫ f)) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f := by
  intro x n
  have h0 : Function.Bijective (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X n x =>
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f rfl a)) := by
    have he : (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X n x =>
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f rfl a)) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (f ≫ f) rfl :=
      funext (fun a => (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_comp n f rfl f rfl rfl a).symm)
    exact he.symm ▸ hf x n
  have h1 : Function.Bijective (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X n (f.app _ x) =>
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f rfl a)) := by
    have he : (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X n (f.app _ x) =>
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f rfl a)) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (f ≫ f) rfl :=
      funext (fun a => (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_comp n f rfl f rfl rfl a).symm)
    exact he.symm ▸ hf (f.app _ x) n
  refine ⟨?_, ?_⟩
  · intro a b hab
    apply h0.injective
    exact congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f (x := f.app _ x) rfl) hab
  · intro y
    obtain ⟨a, ha⟩ := h0.surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f (x := f.app _ x) rfl y)
    refine ⟨a, ?_⟩
    apply h1.injective
    exact congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f (x := f.app _ (f.app _ x)) rfl) ha

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
