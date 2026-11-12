module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeInitialReindex

/-!
概要：初点の対象を固定した coherent simplex に始点の取り替えを適用する。
方針：初点の等式を部分型へ束ね、添字変換に伴う証明の移送を隠す。
規約：パラメータの標的は固定した対象の Hom で、添字変換に依存しない。
使われ方：coherent nerve の coslice の全空間における前合成の単体的構成。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 初点の対象を固定した (n+1) 次 coherent simplex。 -/
def fixedInitialSimplex (z : C) (n : ℕ) :=
  {T : (SimplicialNerve C) _⦋n + 1⦌ // T.obj ⟨ULift.up 0⟩ = z}

/-- 初点固定の標準単体の制限は、固定した初点の対象を保つ。 -/
def fixedInitialSimplexReindex (z : C) {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (T : fixedInitialSimplex z n) : fixedInitialSimplex z m :=
  ⟨(SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α.toOrderHom).uliftMap).comp SSet T.val,
    T.property⟩

/-- 初点が指定した z である simplex の初点を x に取り替える。 -/
def coneInitialFixedSimplex (x : C) {z : C} {n : ℕ} (T : fixedInitialSimplex z n)
    (p : Δ[n] ⟶ (SimplicialCategory.sHom x z).op) :
    (SimplicialNerve C) _⦋n + 1⦌ := by
  rcases T with ⟨T, h⟩
  subst z
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneInitialSimplex x T p

/-- 固定初点の取り替えも、指定した新しい初点を持つ。 -/
lemma coneInitialFixedSimplex_apex (x : C) {z : C} {n : ℕ}
    (T : fixedInitialSimplex z n) (p : Δ[n] ⟶ (SimplicialCategory.sHom x z).op) :
    (SimplicialNerve C).map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op
      (coneInitialFixedSimplex x T p) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x := by
  rcases T with ⟨T, h⟩
  subst z
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneInitialSimplex_apex x T p

/-- 固定初点の取り替えは元の tail を変えない。 -/
lemma coneInitialFixedSimplex_tail (x : C) {z : C} {n : ℕ}
    (T : fixedInitialSimplex z n) (p : Δ[n] ⟶ (SimplicialCategory.sHom x z).op) :
    (SimplicialNerve C).δ 0 (coneInitialFixedSimplex x T p) =
      (SimplicialNerve C).δ 0 T.val := by
  rcases T with ⟨T, h⟩
  subst z
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneInitialSimplex_tail x T p

/-- 固定した初点の対象を変えずに、全ての面・退化とパラメータを同時に制限できる。 -/
lemma coneInitialFixedSimplex_reindex (x : C) {z : C} {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (T : fixedInitialSimplex z n)
    (p : Δ[n] ⟶ (SimplicialCategory.sHom x z).op) :
    (SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α.toOrderHom).uliftMap).comp SSet
        (coneInitialFixedSimplex x T p) =
      coneInitialFixedSimplex x (fixedInitialSimplexReindex z α T) (stdSimplex.map α ≫ p) := by
  rcases T with ⟨T, h⟩
  subst z
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneInitialSimplex_reindex x α T p

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
