module
public import SerrePositivity.KST.SConstruction.SimplexHABeadWordValues
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaCell
public import SerrePositivity.KST.SConstruction.SerreCubeTopMappedComposition

/-! # 元の部分集合 bead 連結語の実 Λ Hom 鎖射
概要：各部分集合の実生成射を、元の Serre tensor 比較と実 dg 合成で連結する。
方針：端点付き連結語と同じ再帰で、同じ自由次元の cube から鎖射を作る。
規約：元の Λ と tensor 射を保持。使われ方：HA 成分からの逆構成の回収式。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の bead 連結語から、元の同じ Λ Hom への実 Serre 鎖射。 -/
def simplexHABeadWordCell {n : ℕ} :
    {a b : Fin (n + 1)} → {d : ℕ} → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b d →
      (serreCubeComplex A d ⟶ homObject A (CubicalLambda A (Δ[n] : SSet.{u}))
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))
  | _, _, _, .bead I hI => simplexSubsetLambdaCell A I hI
  | _, _, _, .join (p := p) (q := q) left right =>
      (serreCubeTensorIso A p q).hom.hom ≫
        (simplexHABeadWordCell left ⊗ₘ simplexHABeadWordCell right) ≫
          eComp (Complex A) _ _ _

end SerrePositivity.KST.SConstruction
