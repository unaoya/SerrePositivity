module
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FunctorMapping

/-! # 元の部分集合 bead 連結語の HA 成分値
概要：HA 成分を各 bead に割り当て、共有端点での通常順合成で連結語を評価する。
方針：元の自由次元の負値を次数として再帰し、厳密 dg 後合成との可換性を示す。
規約：元の native 成分を使い、微分条件はまだ課さない。使われ方：逆 Hom 射の値。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の各 bead の HA 成分と通常順合成による、元の同じ連結語の斉次値。 -/
def simplexHABeadWordValue {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) :
    {a b : Fin (n + 1)} → {d : ℕ} → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b d →
      GradedHom A (s.obj a) (s.obj b) (-(d : ℤ))
  | _, _, _, .bead I hI => s.hom I _ _ _ hI rfl rfl (by omega)
  | _, _, _, .join left right =>
      compose A (simplexHABeadWordValue s right) (simplexHABeadWordValue s left) (by omega)

/-- 元の連結語の評価は、元の厳密 dg 関手による HA 成分の後合成と厳密に可換。 -/
lemma simplexHABeadWordValue_post {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    {E : Type w} [DGCategory A E] (F : DGFunctor A D E)
    {a b : Fin (n + 1)} {d : ℕ} (word : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b d) :
    simplexHABeadWordValue A (s.map F) word =
      (F.map (s.obj a) (s.obj b)).f (-(d : ℤ)) (simplexHABeadWordValue A s word) := by
  induction word with
  | bead I hI => rfl
  | join left right ihL ihR =>
    dsimp only [simplexHABeadWordValue]
    rw [ihL, ihR]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_compose F _ _ _).symm

end SerrePositivity.KST.SConstruction
