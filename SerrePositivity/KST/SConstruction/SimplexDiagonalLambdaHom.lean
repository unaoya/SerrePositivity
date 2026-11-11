module
public import SerrePositivity.KST.SConstruction.SimplexIntervalLambdaHom
public import SerrePositivity.KST.SConstruction.CubicalLambdaCounit

/-! # 元の標準単体の対角 Hom と単位の実同型
概要：同じ頂点の Λ Hom の元の増大と単位は、互いに逆な実鎖射である。
方針：元の零次元区間 Hom 同型と Serre 増大保存を照合する。
規約：元の Hom と元の単位を保持。使われ方：逆 dg 関手の対角・単位と合成の退化場合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded
open scoped ComonObj
variable (A : Type u) [CommRing A]

/-- 元の同じ cube の次元移送は、元の増大を保持する。 -/
lemma serreCubeAugmentation_dimension {n m : ℕ} (h : n = m) :
    eqToHom (congrArg (serreCubeComplex A) h) ≫ serreCubeAugmentation A m =
      serreCubeAugmentation A n := by
  cases h
  exact Category.id_comp _

/-- 元の対角 Λ Hom は、元の零次元区間同型で同じ鎖単位と同型。 -/
def simplexDiagonalLambdaHomIso {N : ℕ} (a : Fin (N + 1)) :
    𝟙_ (Complex A) ≅ homObject A (CubicalLambda A (Δ[N] : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) :=
  eqToIso (congrArg (serreCubeComplex A) (show 0 = a.val - a.val - 1 by omega)) ≪≫
    simplexIntervalLambdaHomIso A a a le_rfl

/-- 元の対角 Hom 同型の順射と元の増大の合成は、元の同じ鎖単位の恒等射。 -/
lemma simplexDiagonalLambdaHomIso_augmentation {N : ℕ} (a : Fin (N + 1)) :
    (simplexDiagonalLambdaHomIso A a).hom ≫
      ((cubicalLambdaCounit.{u, 0} A (Δ[N] : SSet.{u})).map
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a)) = 𝟙 (𝟙_ (Complex A)) := by
  have h := congrArg (fun f => eqToHom (congrArg (serreCubeComplex A)
    (show 0 = a.val - a.val - 1 by omega)) ≫ f)
    (simplexIntervalLambdaHomIso_augmentation A a a le_rfl)
  exact (Category.assoc _ _ _).trans
    (h.trans (serreCubeAugmentation_dimension A (show 0 = a.val - a.val - 1 by omega)))

/-- 元の対角 Hom の増大は、同じ元の対角 Hom 同型の逆射。 -/
lemma simplexDiagonalLambdaHom_augmentation_eq_inv {N : ℕ} (a : Fin (N + 1)) :
    ((cubicalLambdaCounit.{u, 0} A (Δ[N] : SSet.{u})).map
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a)) =
        (simplexDiagonalLambdaHomIso A a).inv := by
  have h := congrArg (fun f => (simplexDiagonalLambdaHomIso A a).inv ≫ f)
    (simplexDiagonalLambdaHomIso_augmentation A a)
  exact ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ ((cubicalLambdaCounit.{u, 0} A (Δ[N] : SSet.{u})).map
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a)))
        (simplexDiagonalLambdaHomIso A a).inv_hom_id).trans (Category.id_comp _))).symm.trans
          (h.trans (Category.comp_id _))

/-- 元の対角 Λ Hom の増大は実同型。 -/
instance simplexDiagonalLambdaHom_augmentation_isIso {N : ℕ} (a : Fin (N + 1)) :
    IsIso ((cubicalLambdaCounit.{u, 0} A (Δ[N] : SSet.{u})).map
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a)) := by
  rw [simplexDiagonalLambdaHom_augmentation_eq_inv A a]
  infer_instance

/-- 元の対角 Hom の単位射は、同じ元の対角 Hom 同型の順射。 -/
lemma simplexDiagonalLambdaHom_id_eq_hom {N : ℕ} (a : Fin (N + 1)) :
    eId (C := CubicalLambda A (Δ[N] : SSet.{u})) (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) =
      (simplexDiagonalLambdaHomIso A a).hom := by
  apply (cancel_mono ((cubicalLambdaCounit.{u, 0} A (Δ[N] : SSet.{u})).map
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a))).1
  exact ((cubicalLambdaCounit.{u, 0} A (Δ[N] : SSet.{u})).map_id (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a)).trans
    (simplexDiagonalLambdaHomIso_augmentation A a).symm

/-- 元の標準単体の対角 Hom の単位射は実同型。 -/
instance simplexDiagonalLambdaHom_id_isIso {N : ℕ} (a : Fin (N + 1)) :
    IsIso (eId (C := CubicalLambda A (Δ[N] : SSet.{u})) (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a)) := by
  rw [simplexDiagonalLambdaHom_id_eq_hom A a]
  infer_instance

end SerrePositivity.KST.SConstruction
