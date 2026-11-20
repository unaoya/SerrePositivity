module


public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIso

/-!
概要：零次数の基点付きの類と基点を選ばない連結成分の界面。
方針：既存の equivPiZero と自然性を使う。
規約：全基点条件から連結成分の全単射性を得る際は源の頂点を明示する。
使われ方：Goerss–Jardine I §§7–8。fiber の零次数の比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra

/-- 概要：単体集合の可換正方形は連結成分上で可換。
方針：二つの合成の関手性を使う。
規約：基点や Kan 性は不要。
使われ方：Goerss–Jardine I §7。fiber の零次数の図式の比較。 -/
theorem mapPiZero_square {A B C D : SSet.{u}} (i : A ⟶ B) (j : C ⟶ D)
    (f : A ⟶ C) (g : B ⟶ D) (comm : i ≫ g = f ≫ j) (a : π₀ A) :
    mapπ₀ g (mapπ₀ i a) = mapπ₀ j (mapπ₀ f a) := by
  rw [← mapπ₀_comp_apply, comm, mapπ₀_comp_apply]

/-- 概要：零次数の類の基点は連結成分の基点の頂点の類に移る。
方針：零単体と頂点の同値の逆関係を使う。
規約：基点 x を固定する。
使われ方：Goerss–Jardine I §7。基点を変えて使う零次数完全列。 -/
@[simp]
theorem KanHomotopyZero.equivPiZero_point {X : SSet.{u}} [KanComplex X] (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point 0 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X 0 x) = π₀.mk x := by
  change π₀.mk ((PtSimplex.equiv₀ x) ((PtSimplex.equiv₀ x).symm x)) = π₀.mk x
  rw [Equiv.apply_symm_apply]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero export _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanHomotopyZero (equivPiZero_point)


/-- 概要：指定基点の零次数の誘導写像の全単射性と連結成分の全単射性は同値。
方針：二つの equivPiZero の自然な可換正方形で移す。
規約：Kan 性は不要で、両側の基点を明示する。
使われ方：Goerss–Jardine I §7。fiber の零次数比較を基点付き界面へ戻す。 -/
theorem KanHomotopyZero.map_bijective_iff_piZero {X Y : SSet.{u}}
    (f : X ⟶ Y) {x : X _⦋0⦌} {y : Y _⦋0⦌} (hf : f.app _ x = y) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.map f hf) ↔ Function.Bijective (mapπ₀ f) := by
  let eX := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (X := X) (x := x)
  let eY := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (X := Y) (x := y)
  have h : eY ∘ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.map f hf = mapπ₀ f ∘ eX := by
    funext a
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero_map f hf a
  calc
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.map f hf) ↔ Function.Bijective (eY ∘ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.map f hf) :=
      (Function.Bijective.of_comp_iff' eY.bijective _).symm
    _ ↔ Function.Bijective (mapπ₀ f ∘ eX) := by rw [h]
    _ ↔ Function.Bijective (mapπ₀ f) := Function.Bijective.of_comp_iff _ eX.bijective

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero export _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanHomotopyZero (map_bijective_iff_piZero)


/-- 概要：源に指定頂点を持つ全基点 π_* 同型は連結成分の全単射を誘導する。
方針：その頂点における零次数の全単射性を二つの equivPiZero で移す。
規約：源が空のときに全基点条件から全射性を推論しない。
使われ方：Goerss–Jardine I §§7–8。fiber の零次数比較の全空間と底。 -/
theorem KanPiIsomorphism.piZero_bijective_at {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {f : X ⟶ Y} (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f) (x : X _⦋0⦌) : Function.Bijective (mapπ₀ f) := by
  let eX := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (X := X) (x := x)
  let eY := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (X := Y) (x := f.app _ x)
  have h : eY ∘ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map 0 f (x := x) rfl = mapπ₀ f ∘ eX := by
    funext a
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero_map f rfl a
  have hb : Function.Bijective (mapπ₀ f ∘ eX) := by
    rw [← h]
    exact eY.bijective.comp (hf x 0)
  exact (Function.Bijective.of_comp_iff _ eX.bijective).1 hb

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
