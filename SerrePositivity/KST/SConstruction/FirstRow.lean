module
public import SerrePositivity.KST.SConstruction.Gapped
public import SerrePositivity.KST.SConstruction.ZeroChoices
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.ZeroBoundaryExtension
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeFamilies
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Definition

/-! # gapped 図式の第一行
概要：F(0,1)→…→F(0,n) への制限を定義する。
方針：正の端点の順序圏から Ar[n] への包含で前合成する。
規約：BGT Lemma 7.3。使われ方：第一行からの相対 cocartesian completion。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：第一行の添字は n 個の正の端点。
方針：Fin n の順序圏の nerve を取る。
規約：n=0 では空の nerve。使われ方：第一行制限の値域。 -/
def firstRowNerve (n : ℕ) : SSet.{u} := nerve (ULift.{u} (Fin n))

/-- 概要：正の端点 j を区間 (0,j) に送る包含。
方針：Fin n の元を succ で正の端点に移す。
規約：最初の零対角を含まない。使われ方：BGT Lemma 7.3 の制限。 -/
def firstRowOrder (n : ℕ) : ULift.{u} (Fin n) →o Ar.{u} n where
  toFun j := arObj 0 j.down.succ (Fin.zero_le _)
  monotone' a b h := ⟨le_rfl, by
    change a.down.succ ≤ b.down.succ
    change a.down.val ≤ b.down.val at h
    exact Nat.add_le_add_right h 1⟩

/-- 概要：第一行の nerve の Ar[n] への包含。
方針：順序関手の nerve。
規約：n=0 も同じ定義。使われ方：第一行制限。 -/
def firstRowInclusion (n : ℕ) : firstRowNerve.{u} n ⟶ arNerve n :=
  nerveMap (firstRowOrder n).toFunctor

/-- 概要：S_n(C) の図式を第一行に制限する。
方針：全部分複体の包含の後で第一行に前合成する。
規約：この定義だけで同値や fibration を主張しない。
使われ方：BGT Lemma 7.3 の実装対象。 -/
def firstRowRestriction (n : ℕ) (C : SSet.{u}) :
    sConstruction n C ⟶ (ihom (firstRowNerve n)).obj C :=
  (gappedSubcomplex n C).ι ≫ (pre (firstRowInclusion n)).app C

/-- 概要：gapped 頂点から元の Ar 図式を取り出す。
方針：内部 Hom の頂点同値を逆向きに使う。
規約：証明は忘れるが選択は加えない。使われ方：第一行の評価式。 -/
def gappedDiagram {n : ℕ} {C : SSet.{u}} (v : (sConstruction n C) _⦋0⦌) :
    arNerve n ⟶ C := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) C).symm v.val

/-- 概要：取り出した図式は gapped である。
方針：充満部分複体の零単体条件を使う。
規約：quasicategory 性は不要。使われ方：相対拡張の始点。 -/
lemma gappedDiagram_isGapped {n : ℕ} {C : SSet.{u}}
    (v : (sConstruction n C) _⦋0⦌) : IsGapped (gappedDiagram v) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v

/-- 概要：第一行制限の頂点は元の図式の前合成を表す。
方針：内部 Hom の前合成を零次元で計算する。
規約：厳密等号。使われ方：第一行を固定した延長の境界条件。 -/
lemma firstRowRestriction_vertex {n : ℕ} {C : SSet.{u}}
    (v : (sConstruction n C) _⦋0⦌) :
    (firstRowRestriction n C).app (Opposite.op ⦋0⦌) v =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (firstRowInclusion n ≫ gappedDiagram v) := by
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (gappedDiagram v) = v.val :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) C).apply_symm_apply v.val
  change ((pre (firstRowInclusion n)).app C).app (Opposite.op ⦋0⦌) v.val = _
  rw [← hv]
  rfl

/-- 概要：正次数の第一行の添字は標準単体。
方針：標準単体と有限順序圏の nerve の既存同型を用いる。
規約：S_(n+1) の第一行は Δ[n]。使われ方：N([n−1]) 表示との照合。 -/
def firstRowSimplexIso (n : ℕ) : (Δ[n] : SSet.{u}) ≅ firstRowNerve (n + 1) :=
  stdSimplex.isoNerve n

end SerrePositivity.KST.SConstruction
