module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares

/-!
概要：同型で結ばれた正方形の二射の、指定基点での π 同型性の比較。
方針：実際の誘導写像の正方形に二つの全単射を合成して打ち消す。
規約：任意基点・零次数を含む。使われ方：loop の fiber 表示による検出。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.KanHomotopy
end SerrePositivity.KST.Spectra.KanHomotopy
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries


/-- 二つの同型で結ばれる射の全単射性は、対応する任意基点で一致する。 -/
lemma map_bijective_iff_of_iso_square {A B C D : SSet.{u}}
    [KanComplex A] [KanComplex B] [KanComplex C] [KanComplex D]
    (eA : A ≅ B) (eC : C ≅ D) (f : A ⟶ C) (g : B ⟶ D)
    (hc : eA.hom ≫ g = f ≫ eC.hom) (a : A _⦋0⦌) (n : ℕ) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f (x := a) rfl) ↔
      Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n g (x := eA.hom.app _ a) rfl) := by
  have hp : eC.hom.app _ (f.app _ a) = g.app _ (eA.hom.app _ a) :=
    (ConcreteCategory.congr_hom (NatTrans.congr_app hc _) a).symm
  let iA := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfIso n eA (x := a) rfl
  let iC := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfIso n eC (x := f.app _ a) hp
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n g (x := eA.hom.app _ a) rfl ∘ iA = iC ∘ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f (x := a) rfl := by
    funext s
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopy.map_square eA.hom eC.hom f g hc rfl hp rfl rfl n s
  calc
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f (x := a) rfl) ↔
        Function.Bijective (iC ∘ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f (x := a) rfl) :=
      (Function.Bijective.of_comp_iff' iC.bijective _).symm
    _ ↔ Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n g (x := eA.hom.app _ a) rfl ∘ iA) := by rw [he]
    _ ↔ Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n g (x := eA.hom.app _ a) rfl) :=
      Function.Bijective.of_comp_iff _ iA.bijective

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy export _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries (map_bijective_iff_of_iso_square)


end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopy.map_bijective_iff_of_iso_square := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.map_bijective_iff_of_iso_square
