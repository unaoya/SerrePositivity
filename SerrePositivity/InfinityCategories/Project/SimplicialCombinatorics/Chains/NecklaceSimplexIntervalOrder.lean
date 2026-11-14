module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FaceDegeneracy.NecklaceSimplexMaps
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FaceDegeneracy.SimplexIntervalMap

/-! # 元の augmentation の区間内の局所頂点番号
概要：標準単体内の全 necklace の頂点像が元の両端の間に入り、局所番号で回収できる。
方針：元の単調性と端点の式を使い、始頂点番号を引いた単調写像を作る。
規約：元の全高次単体の拡張も回収。使われ方：区間 bead への厳密な因数分解。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory Opposite _root_.Simplicial SSet

/-- 元の全 augmentation は、全頂点の単調写像の標準単体への拡張を回収する。 -/
lemma necklaceSimplexMap_eq_extension (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) {n : ℕ}
    (f : T.carrier.{u} ⟶ Δ[n]) :
    T.inclusion ≫ stdSimplex.map (SimplexCategory.Hom.mk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexOrderHom T f)) =
      f := by
  apply SSet.hom_ext
  intro d
  obtain ⟨⟨m⟩⟩ := d
  apply ConcreteCategory.hom_ext
  intro s
  apply stdSimplex.ext
  intro i
  exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap_simplex T f s i).symm

variable {n : ℕ} {a b : Fin (n + 1)}
  (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn (Δ[n] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))

/-- 元の augmentation の始頂点作用は、元の a を回収する。 -/
lemma necklaceInSimplex_vertex_first :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap T.necklace.down T.map T.necklace.down.first = a :=
  congrArg (fun s => s 0) T.map_first

/-- 元の augmentation の終頂点作用は、元の b を回収する。 -/
lemma necklaceInSimplex_vertex_last :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap T.necklace.down T.map T.necklace.down.last = b :=
  congrArg (fun s => s 0) T.map_last

/-- 元の全頂点の像は、元の両端 a,b の間に入る。 -/
lemma necklaceInSimplex_vertex_bounds (v : T.necklace.down.Vertex) :
    a ≤ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap T.necklace.down T.map v ∧
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap T.necklace.down T.map v ≤ b := by
  constructor
  · exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInSimplex_vertex_first T).symm.trans_le
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap_monotone _ T.map (Fin.zero_le v))
  · exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap_monotone _ T.map (Fin.le_last v)).trans_eq
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInSimplex_vertex_last T)

/-- 元の頂点像から始頂点番号を引き、区間の局所番号として読む単調写像。 -/
def necklaceSimplexIntervalOrder :
    T.necklace.down.Vertex →o Fin (b.val - a.val + 1) where
  toFun v := ⟨(_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap T.necklace.down T.map v).val - a.val, by
    have h : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap T.necklace.down T.map v).val ≤ b.val :=
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInSimplex_vertex_bounds T v).2
    omega⟩
  monotone' v w h := by
    change _ - a.val ≤ _ - a.val
    exact Nat.sub_le_sub_right (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap_monotone _ T.map h) _

/-- 元の始頂点の局所番号は零。 -/
lemma necklaceSimplexIntervalOrder_first :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalOrder T T.necklace.down.first = 0 := by
  apply Fin.ext
  change (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap T.necklace.down T.map T.necklace.down.first).val - a.val = 0
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInSimplex_vertex_first, Nat.sub_self]

/-- 元の終頂点の局所番号は区間の最後の番号。 -/
lemma necklaceSimplexIntervalOrder_last :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalOrder T T.necklace.down.last = Fin.last (b.val - a.val) := by
  apply Fin.ext
  change (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap T.necklace.down T.map T.necklace.down.last).val - a.val = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInSimplex_vertex_last]
  rfl

/-- 元の区間の包含に局所番号を合成すると、元の全頂点作用が厳密に戻る。 -/
lemma necklaceSimplexIntervalOrder_comp (hab : a ≤ b) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalOrder a b hab).comp (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalOrder T) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexOrderHom T.necklace.down T.map := by
  apply DFunLike.ext
  intro v
  apply Fin.ext
  change a.val + ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap T.necklace.down T.map v).val - a.val) =
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap T.necklace.down T.map v).val
  have h : a.val ≤ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap T.necklace.down T.map v).val :=
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInSimplex_vertex_bounds T v).1
  omega

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInSimplex_vertex_bounds := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInSimplex_vertex_bounds

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInSimplex_vertex_first := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInSimplex_vertex_first

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInSimplex_vertex_last := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInSimplex_vertex_last

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalOrder (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceSimplexIntervalOrder := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalOrder

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceSimplexIntervalOrder_comp := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalOrder_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceSimplexIntervalOrder_first := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalOrder_first

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceSimplexIntervalOrder_last := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalOrder_last

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceSimplexMap_eq_extension := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexMap_eq_extension

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceSimplexIntervalOrder._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalOrder._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceSimplexIntervalOrder._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalOrder._proof_3
