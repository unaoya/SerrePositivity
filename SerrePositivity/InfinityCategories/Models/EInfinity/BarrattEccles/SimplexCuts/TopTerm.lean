module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Balanced
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra

/-!
模型。文献の定義との比較は後で
# top degree の切断の各項の値

Berger–Fresse §2.2.6 の切断項の、各入力の次数と出力次数が同じ場合の計算。
各色の面写像が恒等になるので、各項の積は同じ cosimplicial 次数での a^r となる。
切断の符号・係数の和・May の比較射の評価はこのモジュールの主張に含めない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open scoped _root_.Simplicial

/-- q+1 個の頂点を持つ色の、元の単体への面写像。 -/
def fullColorFace {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (u : Fin (m + 1) → Fin r) (a : Fin r)
    (hcard : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u a).card = q + 1) :
    (⦋q⦌ : SimplexCategory) ⟶ ⦋q⦌ :=
  SimplexCategory.mkHom ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.fullColorVertices s u a hcard,
    s.vertical.monotone.comp ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u a).orderEmbOfFin hcard).monotone⟩

lemma fullColorFace_eq_id {m q r : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q} {u : Fin (m + 1) → Fin r}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Nondegenerate s u) (a : Fin r) (hcard : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u a).card = q + 1) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.fullColorFace s u a hcard = 𝟙 ⦋q⦌ := by
  ext i
  exact congrArg Fin.val (congrFun (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.fullColorVertices_eq_id h a hcard) i)

/-- BF の切断項の色ごとの積。符号を別に保持するため、ここでは積の部分だけを定義。 -/
def topTerm (X : CosimplicialObject CommRingCat.{u}) {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (u : Fin (m + 1) → Fin r) (hcard : ∀ a, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u a).card = q + 1)
    (a : X.obj ⦋q⦌) : X.obj ⦋q⦌ :=
  ∏ c : Fin r, (X.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.fullColorFace s u c (hcard c))).hom a

/-- 寄与する top degree の各項は、同じ次数の環での r 乗そのもの。 -/
lemma topTerm_eq_power (X : CosimplicialObject CommRingCat.{u}) {m q r : ℕ}
    {s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q} {u : Fin (m + 1) → Fin r} (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Nondegenerate s u)
    (hcard : ∀ a, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u a).card = q + 1) (a : X.obj ⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.topTerm X s u hcard a = a ^ r := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.topTerm
  have he (c : Fin r) : (X.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.fullColorFace s u c (hcard c))).hom a = a := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.fullColorFace_eq_id h, X.map_id]
    rfl
  simp only [he, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
