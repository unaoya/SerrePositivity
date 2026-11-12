module
public import SerrePositivity.KST.SConstruction.SerreCubeFaceTopExt
public import SerrePositivity.KST.SConstruction.SimplexIntervalLambdaHom

/-! # 元の標準単体の実 Λ Hom の全生成元による判定
概要：元の標準単体の順向き区間 Hom からの鎖射を、元の全標準面の最高生成元像で判定。
方針：元の区間 Hom 同型の順射で引き戻し、元の Serre cube の全生成元判定を使う。
規約：元の実 Hom と元の同型を保持。使われ方：native HA からの逆 Hom 射の一意性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の区間 Hom からの鎖射は、同じ実同型を通した全標準面の最高生成元像で決まる。 -/
lemma simplexIntervalLambdaHom_face_top_ext {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b)
    {K : Complex A}
    {f g : homObject A (CubicalLambda A (Δ[n] : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) ⟶ K}
    (h : ∀ (d : ℕ) (v : CubeFaceNormal d (b.val - a.val - 1)),
      serreCubeTopCellImage A K d
          ((serreCubeFaceNormal A v).hom ≫ (simplexIntervalLambdaHomIso A a b hab).hom ≫ f) =
        serreCubeTopCellImage A K d
          ((serreCubeFaceNormal A v).hom ≫ (simplexIntervalLambdaHomIso A a b hab).hom ≫ g)) :
    f = g := by
  apply (cancel_epi (simplexIntervalLambdaHomIso A a b hab).hom).1
  exact serreCube_face_top_image_hom_ext A (b.val - a.val - 1) h

end SerrePositivity.KST.SConstruction
