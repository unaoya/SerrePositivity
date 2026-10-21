module
public import SerrePositivity.KST.SConstruction.NecklaceCategory

/-! # 元の necklace の頂点と単体的写像の頂点作用
概要：necklace の零単体が元の全頂点と一対一に対応することを証明する。
方針：定値単体を逆写像とし、元の包含の全頂点評価を使う。
規約：端点の番号を保持。使われ方：necklace 写像から立方体の頂点作用を作る。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
namespace NecklaceShape

/-- 元の necklace の零単体と、同じ有限順序の全頂点との同値。 -/
def vertexEquiv (T : NecklaceShape) : T.carrier.{u} _⦋0⦌ ≃ T.Vertex where
  toFun x := x.val 0
  invFun v := T.constantSimplex v 0
  left_inv x := by
    apply Subtype.ext
    apply stdSimplex.ext
    intro i
    have hi : i = 0 := by apply Fin.ext; omega
    subst i
    rfl
  right_inv v := rfl

/-- 元の始零単体は、元の始頂点を回収する。 -/
lemma vertexEquiv_first (T : NecklaceShape) : T.vertexEquiv.{u} T.firstVertex = T.first := rfl

/-- 元の終零単体は、元の終頂点を回収する。 -/
lemma vertexEquiv_last (T : NecklaceShape) : T.vertexEquiv.{u} T.lastVertex = T.last := rfl

/-- 一つの bead からなる necklace と、元の標準単体全体との同型。 -/
def singleSimplexIso (n : ℕ) : (single n).carrier.{u} ≅ Δ[n] :=
  SSet.Subcomplex.eqToIso (single_subcomplex_top n) ≪≫ SSet.Subcomplex.topIso _

end NecklaceShape

/-- 元の単体的 necklace 射の全頂点への作用。 -/
def necklaceVertexMap {T U : Necklace.{u}} (f : T ⟶ U) : T.down.Vertex → U.down.Vertex :=
  fun v => U.down.vertexEquiv (f.map.app _ (T.down.vertexEquiv.symm v))

/-- 元の necklace 射の頂点作用は始点を保つ。 -/
lemma necklaceVertexMap_first {T U : Necklace.{u}} (f : T ⟶ U) :
    necklaceVertexMap f T.down.first = U.down.first := by
  change U.down.vertexEquiv (f.map.app _ T.down.firstVertex) = _
  rw [f.map_first, NecklaceShape.vertexEquiv_first]

/-- 元の necklace 射の頂点作用は終点を保つ。 -/
lemma necklaceVertexMap_last {T U : Necklace.{u}} (f : T ⟶ U) :
    necklaceVertexMap f T.down.last = U.down.last := by
  change U.down.vertexEquiv (f.map.app _ T.down.lastVertex) = _
  rw [f.map_last, NecklaceShape.vertexEquiv_last]

/-- 恒等な necklace 射の頂点作用は恒等関数。 -/
lemma necklaceVertexMap_id (T : Necklace.{u}) : necklaceVertexMap (𝟙 T) = _root_.id := by
  funext v
  exact T.down.vertexEquiv.{u}.apply_symm_apply v

/-- 元の necklace 射の合成は、元の全頂点作用の合成。 -/
lemma necklaceVertexMap_comp {T U V : Necklace.{u}} (f : T ⟶ U) (g : U ⟶ V) :
    necklaceVertexMap (f ≫ g) = necklaceVertexMap g ∘ necklaceVertexMap f := by
  funext v
  dsimp only [necklaceVertexMap, Function.comp_apply]
  rw [Equiv.symm_apply_apply]
  rfl

end SerrePositivity.KST.SConstruction
