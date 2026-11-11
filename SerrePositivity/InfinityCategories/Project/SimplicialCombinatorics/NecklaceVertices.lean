module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceCategory

/-! # 元の necklace の頂点と単体的写像の頂点作用
概要：necklace の零単体が元の全頂点と一対一に対応することを証明する。
方針：定値単体を逆写像とし、元の包含の全頂点評価を使う。
規約：端点の番号を保持。使われ方：necklace 写像から立方体の頂点作用を作る。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.SConstruction.NecklaceShape
end SerrePositivity.KST.SConstruction.NecklaceShape
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory _root_.Simplicial SSet
namespace NecklaceShape


/-- 元の necklace の零単体と、同じ有限順序の全頂点との同値。 -/
def vertexEquiv (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : T.carrier.{u} _⦋0⦌ ≃ T.Vertex where
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
lemma vertexEquiv_first (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : T.vertexEquiv.{u} T.firstVertex = T.first := rfl

/-- 元の終零単体は、元の終頂点を回収する。 -/
lemma vertexEquiv_last (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : T.vertexEquiv.{u} T.lastVertex = T.last := rfl

/-- 一つの bead からなる necklace と、元の標準単体全体との同型。 -/
def singleSimplexIso (n : ℕ) : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single n).carrier.{u} ≅ Δ[n] :=
  SSet.Subcomplex.eqToIso (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single_subcomplex_top n) ≪≫ SSet.Subcomplex.topIso _

end NecklaceShape

/-- 元の単体的 necklace 射の全頂点への作用。 -/
def necklaceVertexMap {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ U) : T.down.Vertex → U.down.Vertex :=
  fun v => U.down.vertexEquiv (f.map.app _ (T.down.vertexEquiv.symm v))

/-- 元の necklace 射の頂点作用は始点を保つ。 -/
lemma necklaceVertexMap_first {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ U) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f T.down.first = U.down.first := by
  change U.down.vertexEquiv (f.map.app _ T.down.firstVertex) = _
  rw [f.map_first, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.vertexEquiv_first]

/-- 元の necklace 射の頂点作用は終点を保つ。 -/
lemma necklaceVertexMap_last {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ U) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f T.down.last = U.down.last := by
  change U.down.vertexEquiv (f.map.app _ T.down.lastVertex) = _
  rw [f.map_last, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.vertexEquiv_last]

/-- 恒等な necklace 射の頂点作用は恒等関数。 -/
lemma necklaceVertexMap_id (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (𝟙 T) = _root_.id := by
  funext v
  exact T.down.vertexEquiv.{u}.apply_symm_apply v

/-- 元の necklace 射の合成は、元の全頂点作用の合成。 -/
lemma necklaceVertexMap_comp {T U V : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ U) (g : U ⟶ V) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (f ≫ g) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap g ∘ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f := by
  funext v
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap, Function.comp_apply]
  rw [Equiv.symm_apply_apply]
  rfl

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceVertexMap := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceVertexMap_comp := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceVertexMap_first := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_first

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceVertexMap_id := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_id

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceVertexMap_last := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_last

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.singleSimplexIso := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.vertexEquiv (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.vertexEquiv := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.vertexEquiv

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.vertexEquiv_first := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.vertexEquiv_first

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.vertexEquiv_last := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.vertexEquiv_last

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.vertexEquiv._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.vertexEquiv._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.vertexEquiv._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.vertexEquiv._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.vertexEquiv._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.vertexEquiv._proof_4
