module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIso

/-!
概要：基点を保つ可換正方形による正次数のホモトピー群の可換正方形。
方針：射の合成の関手性と射の等式による移送を使う。
規約：四つの基点保存式を明示する。
使われ方：Goerss–Jardine I §§7–8。fiber の五項列の比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.KanHomotopyGroup
end SerrePositivity.KST.Spectra.KanHomotopyGroup
namespace SerrePositivity.KST.Spectra.KanHomotopy
end SerrePositivity.KST.Spectra.KanHomotopy
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopyGroup


/-- 概要：等しい射と基点保存式は同じ誘導準同型を与える。
方針：射の等式で帰納する。
規約：基点保存の証明は証明の一意性で一致する。
使われ方：Goerss–Jardine I §7。可換図式の写像の比較。 -/
theorem map_congr {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (n : ℕ) {x : X _⦋0⦌} {y : Y _⦋0⦌} {f g : X ⟶ Y} (h : f = g)
    (hf : f.app _ x = y) (hg : g.app _ x = y) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) f hf = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g hg := by
  subst g
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup export _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopyGroup (map_congr)


/-- 概要：基点を保つ単体集合の可換正方形は群の可換正方形を誘導する。
方針：二つの合成写像の誘導準同型を関手性で展開する。
規約：実際の次数は n+1。
使われ方：Goerss–Jardine I §§7–8。長完全列の四角形の可換性。 -/
theorem map_square {A B C D : SSet.{u}}
    [KanComplex A] [KanComplex B] [KanComplex C] [KanComplex D]
    (i : A ⟶ B) (j : C ⟶ D) (f : A ⟶ C) (g : B ⟶ D) (comm : i ≫ g = f ≫ j)
    {a : A _⦋0⦌} {b : B _⦋0⦌} {c : C _⦋0⦌} {d : D _⦋0⦌}
    (hi : i.app _ a = b) (hj : j.app _ c = d)
    (hf : f.app _ a = c) (hg : g.app _ b = d) (n : ℕ)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup A n a) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g hg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map i hi x) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map j hj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f hf x) := by
  have h₁ : (i ≫ g).app _ a = d := by change g.app _ (i.app _ a) = d; rw [hi, hg]
  have h₂ : (f ≫ j).app _ a = d := by change j.app _ (f.app _ a) = d; rw [hf, hj]
  calc
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g hg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map i hi x) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (i ≫ g) h₁ x :=
      (DFunLike.congr_fun (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp i hi g hg h₁) x).symm
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (f ≫ j) h₂ x := DFunLike.congr_fun (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopyGroup.map_congr n comm h₁ h₂) x
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map j hj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f hf x) := DFunLike.congr_fun (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp f hf j hj h₂) x

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup export _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopyGroup (map_square)


end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopyGroup

namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopy


/-- 概要：全自然数次数の誘導写像は射の等式で一致する。
方針：射の等式で帰納する。
規約：零次数も含む。
使われ方：Goerss–Jardine I §7。loop の全次数の自然性。 -/
theorem map_congr {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (n : ℕ) {x : X _⦋0⦌} {y : Y _⦋0⦌} {f g : X ⟶ Y} (h : f = g)
    (hf : f.app _ x = y) (hg : g.app _ x = y) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f hf = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n g hg := by
  subst g
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy export _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopy (map_congr)


/-- 概要：全自然数次数の誘導写像は基点を保つ可換正方形を保つ。
方針：二つの合成の関手性と射の等式の移送を使う。
規約：零次数は集合の写像の等式。
使われ方：Goerss–Jardine I §7。loop と fiber の比較の自然性。 -/
theorem map_square {A B C D : SSet.{u}}
    [KanComplex A] [KanComplex B] [KanComplex C] [KanComplex D]
    (i : A ⟶ B) (j : C ⟶ D) (f : A ⟶ C) (g : B ⟶ D) (comm : i ≫ g = f ≫ j)
    {a : A _⦋0⦌} {b : B _⦋0⦌} {c : C _⦋0⦌} {d : D _⦋0⦌}
    (hi : i.app _ a = b) (hj : j.app _ c = d)
    (hf : f.app _ a = c) (hg : g.app _ b = d) (n : ℕ)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy A n a) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n g hg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n i hi x) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n j hj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f hf x) := by
  have h₁ : (i ≫ g).app _ a = d := by change g.app _ (i.app _ a) = d; rw [hi, hg]
  have h₂ : (f ≫ j).app _ a = d := by change j.app _ (f.app _ a) = d; rw [hf, hj]
  calc
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n g hg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n i hi x) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (i ≫ g) h₁ x := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_comp n i hi g hg h₁ x).symm
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (f ≫ j) h₂ x := congrFun (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopy.map_congr n comm h₁ h₂) x
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n j hj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f hf x) := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_comp n f hf j hj h₂ x

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy export _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopy (map_square)


end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopy

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopy.map_congr := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopy.map_congr

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopy.map_square := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopy.map_square

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.map_congr := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopyGroup.map_congr

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.map_square := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopyGroup.map_square
