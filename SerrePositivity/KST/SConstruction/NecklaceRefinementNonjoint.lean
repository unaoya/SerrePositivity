module
public import SerrePositivity.KST.SConstruction.NecklaceBeadRefinement

/-! # 元の refinement の非 joint 頂点の順序と像
概要：元の necklace の非 joint 頂点を、同じ全頂点を持つ一 bead の内部頂点に含める。
方針：元の両端が joints に含まれることと、元の頂点番号の恒等作用を使う。
規約：元の頂点番号を変えない。使われ方：分割合成の数値座標の順序埋め込み。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction

/-- 元の refinement が誘導する、同じ局所番号を持つ非 joint 頂点の順序埋め込み。 -/
def necklaceRefinementNonjoint (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) : T.down.NonjointVertex ↪o
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).NonjointVertex where
  toFun v := ⟨v.val, by
    intro h
    simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · exact v.property ((congrArg (fun j => j ∈ T.down.joints) h).mpr T.down.zero_mem)
    · exact v.property ((congrArg (fun j => j ∈ T.down.joints) h).mpr T.down.last_mem)⟩
  inj' v w h := Subtype.ext (congrArg
    (fun x : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).NonjointVertex => x.val) h)
  map_rel_iff' := Iff.rfl

/-- 元の非 joint 頂点の包含は、元の全頂点の局所番号を厳密に保持する。 -/
lemma necklaceRefinementNonjoint_val (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) (v : T.down.NonjointVertex) :
    (necklaceRefinementNonjoint T v).val = v.val := rfl

/-- 元の非 joint 包含の像は、元の necklace の joints に入らない同じ内部頂点の全体。 -/
lemma necklaceRefinementNonjoint_range (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    Set.range (necklaceRefinementNonjoint T) = {v | v.val.val ∉ T.down.joints} := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact w.property
  · intro h
    exact ⟨⟨v.val, h⟩, rfl⟩

end SerrePositivity.KST.SConstruction
