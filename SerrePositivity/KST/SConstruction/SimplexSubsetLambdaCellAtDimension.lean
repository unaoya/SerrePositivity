module
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaInclusion

/-! # 元の部分集合 Serre 生成射の指定始域次元
概要：同じ元の部分集合生成射を、濃度次元に等しい指定次元の Serre cube から読む。
方針：元の始域の次元移送を前合成し、部分集合の等号との整合性を示す。
規約：元の端点と実鎖射を保持。使われ方：読み替えと同じ次元での標準面比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の同端点の部分集合生成射を、同じ濃度次元に等しい指定次元から読む。 -/
def simplexSubsetLambdaCellAtDimension {n : ℕ} (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (hI : 2 ≤ I.card) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (d : ℕ) (hd : d = I.card - 2) :
    serreCubeComplex A d ⟶ homObject A (CubicalLambda A (Δ[n] : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) :=
  eqToHom (congrArg (serreCubeComplex A) hd) ≫ simplexSubsetLambdaCellAt A I a b hI ha hb

/-- 元の濃度次元を指定すれば、元の同端点の部分集合生成射を回収する。 -/
lemma simplexSubsetLambdaCellAtDimension_refl {n : ℕ} (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (hI : 2 ≤ I.card) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) :
    simplexSubsetLambdaCellAtDimension A I a b hI ha hb (I.card - 2) rfl =
      simplexSubsetLambdaCellAt A I a b hI ha hb := Category.id_comp _

/-- 元の部分集合が等しければ、同じ指定次元・同じ端点の実生成射も厳密に一致する。 -/
lemma simplexSubsetLambdaCellAtDimension_congr {n : ℕ} (I J : Finset (Fin (n + 1)))
    (hIJ : I = J) (a b : Fin (n + 1)) (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card)
    (haI : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hbI : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (haJ : a = J.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty J hJ))
    (hbJ : b = J.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty J hJ))
    (d : ℕ) (hdI : d = I.card - 2) (hdJ : d = J.card - 2) :
    simplexSubsetLambdaCellAtDimension A I a b hI haI hbI d hdI =
      simplexSubsetLambdaCellAtDimension A J a b hJ haJ hbJ d hdJ := by
  cases hIJ
  rfl

/-- 元の指定端点・次元の生成射は、元の同じ部分集合の実生成射と異種等号で一致。 -/
lemma simplexSubsetLambdaCellAtDimension_canonical_heq {n : ℕ}
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (d : ℕ) (hd : d = I.card - 2) :
    HEq (simplexSubsetLambdaCellAtDimension A I a b hI ha hb d hd)
      (simplexSubsetLambdaCell A I hI) := by
  subst a b d
  simp only [simplexSubsetLambdaCellAtDimension_refl]
  rfl

/-- 元の部分集合の等号は、元の同じ実生成射の異種等号を与える。 -/
lemma simplexSubsetLambdaCell_heq_of_eq {n : ℕ} (I J : Finset (Fin (n + 1)))
    (hIJ : I = J) (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) :
    HEq (simplexSubsetLambdaCell A I hI) (simplexSubsetLambdaCell A J hJ) := by
  cases hIJ
  rfl

end SerrePositivity.KST.SConstruction
