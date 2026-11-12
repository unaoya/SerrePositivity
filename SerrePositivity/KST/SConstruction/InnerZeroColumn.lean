module
public import SerrePositivity.KST.SConstruction.InnerDiagonalComponents
public import SerrePositivity.KST.SConstruction.DiagonalIterationRealization
public import SerrePositivity.KST.SConstruction.BoundaryReduction

/-! # 内側の零列の最後の零方向への包含
概要：反復実現の内側の零列が既存の最後の零方向に入ることを示す。
方針：次数ごとに自己関手の比較の成分を core へ移し、零方向の包含の可換式を評価する。
規約：部分複体の像を保ち、高次単体も含む。使われ方：全零境界商への降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：内側の零列の単体を最後の零方向の実現の単体に移す。
方針：零方向の比較の成分を忘却関手と core で写して同じ次数で評価する。
規約：次数ごとの関数。使われ方：零方向の像の包含の証人。 -/
def iteratedZeroColumnLastZeroPreimage (r : ℕ) (X : StableModel.{u}) (n : ℕ) :
    ((iteratedSRealizationDiagram r X).obj (Opposite.op ⦋0⦌)).obj (Opposite.op ⦋n⦌) →
      (simplicialDiagonalFunctor.obj (zeroDirectionsDiagram {Fin.last r} X)).obj
        (Opposite.op ⦋n⦌) :=
  (((stableModelForget ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor).map
    ((innerZeroDirectionComparisonIso r n).hom.app X)).app (Opposite.op ⦋n⦌))

/-- 概要：零列の単体の像は最後の零方向の包含で厳密に回収される。
方針：自己関手の包含の可換式を入力、core、単体で順に評価する。
規約：既存の反復実現の座標同型を使う。使われ方：全零境界に入ることの証明。 -/
lemma iteratedZeroColumnLastZeroPreimage_fac (r : ℕ) (X : StableModel.{u}) (n : ℕ)
    (x : ((iteratedSRealizationDiagram r X).obj (Opposite.op ⦋0⦌)).obj (Opposite.op ⦋n⦌)) :
    ((zeroDirectionsInclusion {Fin.last r} X).app (Opposite.op ⦋n⦌))
        (iteratedZeroColumnLastZeroPreimage r X n x) =
      ((diagonalZeroColumn (iteratedSRealizationDiagram r X) ≫
        (iteratedSRealizationCoordinateIso r X).hom).app (Opposite.op ⦋n⦌)) x := by
  let H := stableModelForget.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor
  have h := innerZeroDirectionComparisonIso_inclusion.{u} r n
  rw [← diagonalSInnerComparisonNatIso_app_eq_inner] at h
  have hh := congrArg (fun f => (H.map f).app (Opposite.op ⦋n⦌) x)
    (NatTrans.congr_app h X)
  simp only [NatTrans.comp_app] at hh
  simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app] at hh
  exact hh.symm

/-- 概要：座標同型の下で内側の零列の像は全零境界に含まれる。
方針：各単体の最後の零方向での原像と、有限合併への包含を使う。
規約：全次数の部分複体の包含。使われ方：境界商への降下。 -/
lemma iteratedZeroColumn_range_le_fatBoundary (r : ℕ) (X : StableModel.{u}) :
    Subcomplex.range (diagonalZeroColumn (iteratedSRealizationDiagram r X) ≫
      (iteratedSRealizationCoordinateIso r X).hom) ≤ zeroDirectionsFatBoundary (r + 1) X := by
  have hlast : zeroDirectionsRange {Fin.last r} X ≤ zeroDirectionsFatBoundary (r + 1) X := by
    exact Finset.le_sup (f := fun i => zeroDirectionsRange (insert i ∅) X) (Finset.mem_univ _)
  apply le_trans ?_ hlast
  intro d z hz
  obtain ⟨x, rfl⟩ := hz
  exact ⟨iteratedZeroColumnLastZeroPreimage r X d.unop.len x,
    iteratedZeroColumnLastZeroPreimage_fac r X d.unop.len x⟩

/-- 概要：内側の零列から全零境界への実際の単体的写像。
方針：像の包含により部分複体へ持ち上げる。
規約：次数ごとの原像の選択には依存しない。使われ方：境界商の基点条件。 -/
def iteratedZeroColumnFatBoundaryLift (r : ℕ) (X : StableModel.{u}) :
    (iteratedSRealizationDiagram r X).obj (Opposite.op ⦋0⦌) ⟶
      (zeroDirectionsFatBoundary (r + 1) X : SSet.{u}) :=
  Subcomplex.lift (diagonalZeroColumn (iteratedSRealizationDiagram r X) ≫
    (iteratedSRealizationCoordinateIso r X).hom) (iteratedZeroColumn_range_le_fatBoundary r X)

/-- 概要：境界への持ち上げは座標同型による零列の像を厳密に回収する。
方針：部分複体への持ち上げの回収式。
規約：全単体での等号。使われ方：cofiber の降下条件。 -/
lemma iteratedZeroColumnFatBoundaryLift_ι (r : ℕ) (X : StableModel.{u}) :
    iteratedZeroColumnFatBoundaryLift r X ≫ (zeroDirectionsFatBoundary (r + 1) X).ι =
      diagonalZeroColumn (iteratedSRealizationDiagram r X) ≫
        (iteratedSRealizationCoordinateIso r X).hom := Subcomplex.lift_ι _ _

end SerrePositivity.KST.SConstruction
