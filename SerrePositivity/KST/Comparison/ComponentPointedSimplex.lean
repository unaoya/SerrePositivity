module

public import SerrePositivity.KST.Comparison.ComponentKan
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyGroups

/-!
# 境界定数単体を選ばれた成分へ持ち上げる

概要：正次数の境界定数単体は基点と同じ連結成分に入る。
方針：一つの定数な面と単体の成分の一致を使って全単体を持ち上げる。
規約：KST Lemma 2.13 の高次の可逆成分の比較。π_n の代表は K-L9 から借りる。
使われ方：成分全体の包含の正次数のホモトピー群の全射性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite SSet
open scoped _root_.Simplicial

/--
概要：定数写像が表す単体の成分はその定数の頂点の成分である。
方針：最初の頂点の引き戻しを Yoneda の自然性で計算する。
規約：任意の単体次数。
使われ方：境界定数単体の成分の検査。
-/
theorem simplexClass_yoneda_const (X : SSet.{u}) (x : X _⦋0⦌) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass X (yonedaEquiv (SSet.const (X := Δ[n]) x)) = π₀.mk x := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexVertex
  rw [yonedaEquiv_naturality, SSet.comp_const, yonedaEquiv_const]

/--
概要：正次数の境界定数単体の成分は基点の成分である。
方針：零番目の面の定数性と面での成分の不変性を使う。
規約：Kan 性を仮定しない。
使われ方：全ての境界定数単体を選んだ部分複体へ持ち上げる。
-/
theorem pointedSimplex_class (X : SSet.{u}) {n : ℕ} {x : X _⦋0⦌}
    (s : X.PtSimplex (n + 1) x) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass X (yonedaEquiv s.map) = π₀.mk x := by
  have h := congrArg yonedaEquiv (s.δ_map (0 : Fin (n + 2)))
  rw [stdSimplex.yonedaEquiv_δ_comp] at h
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass X (X.map (SimplexCategory.δ (0 : Fin (n + 2))).op
        (yonedaEquiv s.map)) := (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass_map X _ _).symm
    _ = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass X (yonedaEquiv (SSet.const (X := Δ[n]) x)) := congrArg (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass X) h
    _ = _ := simplexClass_yoneda_const X x n

/--
概要：選んだ基点における境界定数単体を成分部分複体へ持ち上げる。
方針：単体の成分と基点の成分の一致で単体を持ち上げ、包含後で境界条件を検査する。
規約：正次数。基点は部分複体の実際の頂点として与える。
使われ方：正次数のホモトピー群の代表の持ち上げ。
-/
def componentPtSimplexLift (X : SSet.{u}) (P : π₀ X → Prop)
    (x : (componentSubcomplex X P : SSet) _⦋0⦌) {n : ℕ}
    (s : X.PtSimplex (n + 1) x.val) :
    (componentSubcomplex X P : SSet).PtSimplex (n + 1) x where
  map := componentSimplexLift X P s.map (by
    rw [pointedSimplex_class]
    exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass_zero X x.val) ▸ x.property)
  comm := by
    apply (cancel_mono (componentSubcomplex X P).ι).mp
    rw [Category.assoc, componentSimplexLift_ι, s.comm]
    simp only [Subcomplex.ofSimplex_ι, SSet.const_comp]
    rfl

/--
概要：境界定数単体の持ち上げは包含後に元の代表へ戻る。
方針：相対写像の基礎写像を比較し、単体の持ち上げの分解式を使う。
規約：境界条件の証明の選択に依存しない。
使われ方：正次数のホモトピー群の全射性。
-/
theorem componentPtSimplexLift_map (X : SSet.{u}) (P : π₀ X → Prop)
    (x : (componentSubcomplex X P : SSet) _⦋0⦌) {n : ℕ}
    (s : X.PtSimplex (n + 1) x.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (componentSubcomplex X P).ι rfl (componentPtSimplexLift X P x s) = s := by
  apply RelativeMorphism.ext
  exact componentSimplexLift_ι X P s.map _

end SerrePositivity.KST.Comparison
