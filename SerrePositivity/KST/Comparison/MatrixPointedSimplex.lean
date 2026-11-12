module

public import SerrePositivity.KST.Comparison.MatrixSpace
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyGroups

/-!
# 係数ごとの境界定数単体と関係を行列へまとめる

概要：行列の境界定数単体と RelStruct は係数ごとに構成できる。
方針：全ての係数の実際の射を行列へ束ね、面条件を係数評価後で確認する。
規約：KST Lemma 2.13 の高次の行列公式の代表の構成。
使われ方：ホモトピー群の行列の積分解の全単射性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite SSet
open scoped Simplicial

/--
概要：行列を値とする単体写像は全係数で一致すれば等しい。
方針：各次数の行列を係数で比較する。
規約：定義域は任意の単体集合。
使われ方：束ねた写像の境界と面の検査。
-/
theorem matrixMap_ext (A : SimplicialObject RingCat.{u}) (r : ℕ) {X : SSet.{u}}
    {f g : X ⟶ matrixSpace A r}
    (h : ∀ i j : Fin r, f ≫ matrixEntryMap A r i j = g ≫ matrixEntryMap A r i j) : f = g := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro x
  apply Matrix.ext
  intro i j
  exact congrArg (fun q => q.app d x) (h i j)

/--
概要：係数を束ねた写像の各係数は元の写像である。
方針：各次数で定義を計算する。
規約：全ての行・列に対する厳密な等式。
使われ方：面の等式を係数へ戻す。
-/
@[reassoc] theorem matrixMapOfEntries_entry (A : SimplicialObject RingCat.{u}) (r : ℕ)
    {X : SSet.{u}} (f : Fin r → Fin r → (X ⟶ ringSpace A)) (i j : Fin r) :
    matrixMapOfEntries A r f ≫ matrixEntryMap A r i j = f i j := rfl

/--
概要：係数ごとの境界定数単体を行列の境界定数単体へまとめる。
方針：写像を束ね、境界条件を全係数で検査する。
規約：基点行列の各係数を各代表の基点とする。
使われ方：行列のホモトピー群の係数写像の全射性。
-/
def matrixPtSimplex (A : SimplicialObject RingCat.{u}) (r n : ℕ)
    (a : (matrixSpace A r) _⦋0⦌)
    (f : ∀ i j : Fin r, (ringSpace A).PtSimplex n (a i j)) :
    (matrixSpace A r).PtSimplex n a where
  map := matrixMapOfEntries A r (fun i j => (f i j).map)
  comm := by
    apply matrixMap_ext A r
    intro i j
    rw [Category.assoc, matrixMapOfEntries_entry]
    simp only [Subcomplex.ofSimplex_ι, SSet.comp_const, SSet.const_comp]
    change (boundary n).ι ≫ (f i j).map = SSet.const (a i j)
    simpa only [Subcomplex.ofSimplex_ι, SSet.comp_const] using (f i j).comm

/--
概要：行列の境界定数単体の各係数は指定した代表である。
方針：相対写像の基礎写像を定義で計算する。
規約：基点の像は係数評価そのもの。
使われ方：ホモトピー類の代表計算。
-/
theorem matrixPtSimplex_entry (A : SimplicialObject RingCat.{u}) (r n : ℕ)
    (a : (matrixSpace A r) _⦋0⦌)
    (f : ∀ i j : Fin r, (ringSpace A).PtSimplex n (a i j)) (i j : Fin r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (matrixEntryMap A r i j) rfl (matrixPtSimplex A r n a f) = f i j := by
  apply RelativeMorphism.ext
  rfl

/--
概要：同じ面添字の係数ごとの RelStruct を行列の RelStruct へまとめる。
方針：充填の写像を束ね、全ての指定された面を係数評価後で確認する。
規約：Kan 性はこの実際の充填の組み立てには不要。
使われ方：係数評価による正次数のホモトピー群の単射性。
-/
def matrixRelStruct (A : SimplicialObject RingCat.{u}) (r n : ℕ)
    (a : (matrixSpace A r) _⦋0⦌) {f g : (matrixSpace A r).PtSimplex n a} {k : Fin (n + 1)}
    (h : ∀ i j : Fin r, PtSimplex.RelStruct
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (matrixEntryMap A r i j) rfl f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (matrixEntryMap A r i j) rfl g) k) : PtSimplex.RelStruct f g k where
  map := matrixMapOfEntries A r (fun i j => (h i j).map)
  δ_castSucc_map := by
    apply matrixMap_ext A r
    intro i j
    rw [Category.assoc, matrixMapOfEntries_entry]
    exact (h i j).δ_castSucc_map
  δ_succ_map := by
    apply matrixMap_ext A r
    intro i j
    rw [Category.assoc, matrixMapOfEntries_entry]
    exact (h i j).δ_succ_map
  δ_map_of_lt l hl := by
    apply matrixMap_ext A r
    intro i j
    rw [Category.assoc, matrixMapOfEntries_entry, SSet.const_comp]
    exact (h i j).δ_map_of_lt l hl
  δ_map_of_gt l hl := by
    apply matrixMap_ext A r
    intro i j
    rw [Category.assoc, matrixMapOfEntries_entry, SSet.const_comp]
    exact (h i j).δ_map_of_gt l hl

end SerrePositivity.KST.Comparison
