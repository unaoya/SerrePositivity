module

public import SerrePositivity.EInfinity.SimplexCuts.Balanced
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra

/-!
# top degree の切断の各項の値

Berger–Fresse §2.2.6 の切断項の、各入力の次数と出力次数が同じ場合の計算。
各色の面写像が恒等になるので、各項の積は同じ cosimplicial 次数での a^r となる。
切断の符号・係数の和・May の比較射の評価はこのモジュールの主張に含めない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open scoped Simplicial

/-- q+1 個の頂点を持つ色の、元の単体への面写像。 -/
def fullColorFace {m q r : ℕ} (s : Cut m q) (u : Fin (m + 1) → Fin r) (a : Fin r)
    (hcard : (colorPositions s u a).card = q + 1) :
    (⦋q⦌ : SimplexCategory) ⟶ ⦋q⦌ :=
  SimplexCategory.mkHom ⟨fullColorVertices s u a hcard,
    s.vertical.monotone.comp ((colorPositions s u a).orderEmbOfFin hcard).monotone⟩

lemma fullColorFace_eq_id {m q r : ℕ} {s : Cut m q} {u : Fin (m + 1) → Fin r}
    (h : Nondegenerate s u) (a : Fin r) (hcard : (colorPositions s u a).card = q + 1) :
    fullColorFace s u a hcard = 𝟙 ⦋q⦌ := by
  ext i
  exact congrArg Fin.val (congrFun (fullColorVertices_eq_id h a hcard) i)

/-- BF の切断項の色ごとの積。符号を別に保持するため、ここでは積の部分だけを定義。 -/
def topTerm (X : CosimplicialObject CommRingCat.{u}) {m q r : ℕ} (s : Cut m q)
    (u : Fin (m + 1) → Fin r) (hcard : ∀ a, (colorPositions s u a).card = q + 1)
    (a : X.obj ⦋q⦌) : X.obj ⦋q⦌ :=
  ∏ c : Fin r, (X.map (fullColorFace s u c (hcard c))).hom a

/-- 寄与する top degree の各項は、同じ次数の環での r 乗そのもの。 -/
lemma topTerm_eq_power (X : CosimplicialObject CommRingCat.{u}) {m q r : ℕ}
    {s : Cut m q} {u : Fin (m + 1) → Fin r} (h : Nondegenerate s u)
    (hcard : ∀ a, (colorPositions s u a).card = q + 1) (a : X.obj ⦋q⦌) :
    topTerm X s u hcard a = a ^ r := by
  unfold topTerm
  have he (c : Fin r) : (X.map (fullColorFace s u c (hcard c))).hom a = a := by
    rw [fullColorFace_eq_id h, X.map_id]
    rfl
  simp only [he, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end SerrePositivity.EInfinity.SimplexCuts
