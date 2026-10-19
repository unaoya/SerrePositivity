module

public import SerrePositivity.KST.Spectra.PointedSkeletalMappingTower

/-!
概要：一頂点の単体集合の零骨格は一点と同型。
方針：零骨格を頂点の生成部分複体と同定し、各次数の単体の一意性を使う。
規約：頂点を明示するので空の単体集合は含まない。
使われ方：Goerss–Jardine VIII §2。零骨格への制限を頂点評価へ読み替える。
-/

@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.UnbasedPointedMapping

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K : SSet.{u}) [Subsingleton (K _⦋0⦌)] (v : K _⦋0⦌)

/-- 零骨格は選んだ頂点が生成する部分複体。 -/
lemma zeroSkeleton_eq_ofSimplex : K.skeleton 1 = Subcomplex.ofSimplex v := by
  apply le_antisymm
  · rw [show 1 = 0 + 1 from rfl, K.skeleton_succ, K.skeleton_zero, bot_sup_eq]
    apply iSup_le
    intro x
    rw [show x.val = v from Subsingleton.elim _ _]
  · exact K.ofSimplex_le_skeleton v (by decide)

include v in
/-- 一頂点の零骨格の各次数の単体は一意。 -/
lemma zeroSkeleton_obj_subsingleton (m : SimplexCategoryᵒᵖ) :
    Subsingleton ((K.skeleton 1 : SSet.{u}).obj m) := by
  change Subsingleton {x : K.obj m // x ∈ (K.skeleton 1).obj m}
  rw [zeroSkeleton_eq_ofSimplex K v]
  refine ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ ?_⟩
  apply Subtype.ext
  obtain ⟨f, rfl⟩ := (Subcomplex.mem_ofSimplex_obj_iff v a).1 ha
  obtain ⟨g, rfl⟩ := (Subcomplex.mem_ofSimplex_obj_iff v b).1 hb
  change K.map f.op v = K.map g.op v
  exact congrArg (fun h ↦ K.map h.op v) (Subsingleton.elim f g)

/-- 選んだ頂点を零骨格へ持ち上げる一点からの射。 -/
def initialVertexMap : (𝟙_ SSet.{u}) ⟶ (K.skeleton 1 : SSet.{u}) :=
  SSet.const ⟨v, K.mem_skeleton v (by decide)⟩

/-- 一点と一頂点の零骨格の同型。 -/
def initialVertexIso : (𝟙_ SSet.{u}) ≅ (K.skeleton 1 : SSet.{u}) where
  hom := initialVertexMap K v
  inv := toUnit _
  hom_inv_id := isTerminalTensorUnit.hom_ext _ _
  inv_hom_id := by
    ext m a
    exact (zeroSkeleton_obj_subsingleton K v m).elim _ _

/-- 零骨格への頂点射は同型。 -/
instance initialVertexMap_isIso : IsIso (initialVertexMap K v) :=
  inferInstanceAs (IsIso (initialVertexIso K v).hom)

omit [Subsingleton (K _⦋0⦌)] in
/-- 持ち上げた頂点の包含は元の定数頂点射。 -/
lemma initialVertexMap_ι : initialVertexMap K v ≫ (K.skeleton 1).ι = SSet.const v := by
  rw [initialVertexMap, SSet.const_comp]
  rfl

end
end SerrePositivity.KST.Spectra.UnbasedPointedMapping
