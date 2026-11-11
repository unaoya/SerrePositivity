module
public import SerrePositivity.KST.SConstruction.SimplexDiagonalLambdaHom

/-! # 元の対角 Λ Hom の非零次数での消滅
概要：元の標準単体の同じ頂点間の Λ Hom は、零次数以外で実際に零対象。
方針：元の対角 Hom と鎖単位の実同型を各次数で評価する。
規約：元の Hom と次数を保持。使われ方：像が一点の高次退化 HA 成分の零性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の対角 Λ Hom の非零次数の加群は、元の鎖単位の同じ次数とともに零対象。 -/
lemma simplexDiagonalLambdaHom_X_isZero {N : ℕ} (a : Fin (N + 1)) (k : ℤ) (hk : k ≠ 0) :
    IsZero ((homObject A (CubicalLambda A (SSet.stdSimplex.obj (SimplexCategory.mk N)))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a)).X k) :=
  (isZero_single_obj_X (.up ℤ) 0 (𝟙_ (ModuleCat A)) k hk).of_iso
    (((HomologicalComplex.eval (ModuleCat A) (.up ℤ) k).mapIso
      (simplexDiagonalLambdaHomIso A a)).symm)

end SerrePositivity.KST.SConstruction
