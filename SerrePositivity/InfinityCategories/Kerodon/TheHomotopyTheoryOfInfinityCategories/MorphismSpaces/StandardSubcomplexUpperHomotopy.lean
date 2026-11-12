module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.StandardUpperVertexHomotopy

/-!
# 標準単体の部分複体への最大値の変形の制限

概要：最大値への変形を保つ部分複体には同じ変形を内部のホモトピーとして制限できる。
方針：全変形の像の所属を使って射を持ち上げ、両端を単体の公式で確かめる。
規約：安定性は変形全体の条件で、終端の写像の安定性だけとは区別する。
使われ方：HA 1.3.1.17、Kerodon Proposition 4.6.7.23（Tag 01LW） の標準ホーンと面への共通の適用。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open CategoryTheory MonoidalCategory
open scoped _root_.Simplicial

/-- 概要：標準単体の部分複体が最大値への変形の全ての値を含むという条件。
方針：部分複体の各単体と単位区間の各単体で所属を要求する。
規約：同じ標準単体の次数 n を固定する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） のホーンと面の変形への共通の入口。 -/
def StandardUpperStable {n : ℕ} (A : (Δ[n] : SSet.{u}).Subcomplex) (i : Fin (n + 1)) : Prop :=
  ∀ {d : ℕ} (σ : (Δ[n] : SSet.{u}) _⦋d⦌), σ ∈ A.obj (Opposite.op ⦋d⦌) →
    ∀ t : (Δ[1] : SSet.{u}) _⦋d⦌,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.standardUpperVertexHomotopyMap i).app (Opposite.op ⦋d⦌) (σ, t) ∈ A.obj (Opposite.op ⦋d⦌)

/-- 概要：安定な部分複体と単位区間の積へ標準単体の変形を制限する。
方針：全変形中の所属を使って部分複体へ持ち上げる。
規約：包含後に元の変形の各単体を保つ。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の標準ホーン内のホモトピーの台。 -/
def standardSubcomplexUpperHomotopyMap {n : ℕ} (A : (Δ[n] : SSet.{u}).Subcomplex)
    (i : Fin (n + 1)) (hA : StandardUpperStable A i) : A.toSSet ⊗ Δ[1] ⟶ A.toSSet :=
  SSet.Subcomplex.lift ((A.ι ▷ Δ[1]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.standardUpperVertexHomotopyMap i) (by
    intro d σ hσ
    obtain ⟨⟨d⟩⟩ := d
    obtain ⟨G, rfl⟩ := hσ
    exact hA G.1.val G.1.property G.2)

/-- 概要：安定な部分複体内の変形の一端点による自己写像。
方針：単位区間の一端点で制限した変形を評価する。
規約：包含後に頂点との最大値による標準単体の自己写像に一致する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の面とホーンの合成の記述。 -/
def standardSubcomplexUpperMap {n : ℕ} (A : (Δ[n] : SSet.{u}).Subcomplex)
    (i : Fin (n + 1)) (hA : StandardUpperStable A i) : A.toSSet ⟶ A.toSSet :=
  SSet.ι₁ ≫ standardSubcomplexUpperHomotopyMap A i hA

/-- 概要：制限した一端点の射は包含後に標準単体の最大値の自己写像と一致する。
方針：各頂点で変形の値の公式の一端点を評価する。
規約：実際の単体集合の射の等式。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の部分複体内の因子分解の照合。 -/
lemma standardSubcomplexUpperMap_ι {n : ℕ} (A : (Δ[n] : SSet.{u}).Subcomplex)
    (i : Fin (n + 1)) (hA : StandardUpperStable A i) :
    standardSubcomplexUpperMap A i hA ≫ A.ι =
      A.ι ≫ SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionUpperVertexMap i)) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro σ
  apply SSet.stdSimplex.ext
  intro r
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.standardUpperVertexHomotopyMap_apply i σ.val _ r

/-- 概要：安定な部分複体の恒等射は制限した最大値の自己写像とホモトピックである。
方針：零端点を単体の公式で確かめ、一端点は自己写像の定義を使う。
規約：部分複体自身の Kan 性は要求しない。
使われ方：HA 1.3.1.17 の標準ホーン側での Kan 標的の比較。 -/
def standardSubcomplexUpperHomotopy {n : ℕ} (A : (Δ[n] : SSet.{u}).Subcomplex)
    (i : Fin (n + 1)) (hA : StandardUpperStable A i) :
    SSet.Homotopy (𝟙 A.toSSet) (standardSubcomplexUpperMap A i hA) where
  h := standardSubcomplexUpperHomotopyMap A i hA
  h₀ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    apply SSet.stdSimplex.ext
    intro r
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.standardUpperVertexHomotopyMap_apply i σ.val _ r
  h₁ := rfl
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.2

/-- 概要：安定な部分複体上の最大値の自己写像は Kan 標的の前合成の同値条件を満たす。
方針：同じ部分複体内の恒等射からのホモトピーと同値性の不変性を使う。
規約：部分複体自体の Kan 性は不要。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の標準ホーンと面の合成の比較。 -/
lemma standardSubcomplexUpperMap_isKanPrecompositionEquivalence {n : ℕ}
    (A : (Δ[n] : SSet.{u}).Subcomplex) (i : Fin (n + 1)) (hA : StandardUpperStable A i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsKanPrecompositionEquivalence (standardSubcomplexUpperMap A i hA) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isKanPrecompositionEquivalence_iff_of_homotopy
    (standardSubcomplexUpperHomotopy A i hA)).mp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isKanPrecompositionEquivalence_id _)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
