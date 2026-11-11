module
public import SerrePositivity.KST.SConstruction.SimplexHABeadWordCells
public import SerrePositivity.KST.SConstruction.CubicalLambdaNativeCellComponent

/-! # 元の bead 連結語の HA 値と実鎖射の回収
概要：実 dg 関手からの HA 成分で連結語を評価すると、元の実鎖射の最高生成元像に戻る。
方針：各 bead の回収と元の Serre tensor・dg 合成の向き付き評価で帰納する。
規約：元の鎖射と指定次数を保持。使われ方：全生成元への HA 値の割り当ての逆律。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の実 dg 関手の HA 連結語値は、同じ実鎖射の向き付き最高生成元像を回収する。 -/
lemma simplexHABeadWordValue_recovery {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    {a b : Fin (n + 1)} {d : ℕ} (word : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b d) :
    simplexHABeadWordValue A (cubicalLambdaNativeSimplexData A F) word =
      serreCubeTopCellImage A _ d (simplexHABeadWordCell A word ≫ F.map _ _) := by
  induction word with
  | bead I hI =>
    dsimp only [simplexHABeadWordValue, simplexHABeadWordCell]
    have h := cubicalLambdaNativeSimplexData_hom_cell A F I _ _
      (-((I.card - 2 : ℕ) : ℤ)) hI rfl rfl (by omega)
    simpa only [eqToHom_refl, CategoryTheory.id_apply] using h
  | join left right ihL ihR =>
    dsimp only [simplexHABeadWordValue, simplexHABeadWordCell]
    rw [ihL, ihR]
    exact (serreCubeTopCellImage_composition_post A F _ _ _ _).symm

end SerrePositivity.KST.SConstruction
