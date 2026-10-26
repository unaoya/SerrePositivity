module
public import SerrePositivity.KST.SConstruction.Cofinality.CokernelStructureMaps

/-!
概要：元の K₀ 余核を全 S 多次数の厳密な可換群値図式へ束ねる。
方針：各余核類を一つの対象で表し、元の S 構造射の関手則で検査する。
規約：全多次数を独立に保持する。
使われ方：離散的障害の bar 図式の組立。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の標的の頂点の余核類は K₀ 余核へ全射。
方針：余核類を K₀ 類へ持ち上げ、一つの対象頂点で表す。
規約：完備化証拠を必要としない。
使われ方：余核準同型の一致を元の頂点で検査する。 -/
lemma completionKZeroVertexClass_surjective (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    Function.Surjective (completionKZeroVertexClass r ι f) := by
  intro z
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective z
  obtain ⟨y, hy⟩ := completionKZeroVertex_surjective r ι Y a
  exact ⟨y, congrArg (QuotientAddGroup.mk'
    (triangulatedKZeroSourceMap (((multiSEndofunctor r).obj ι).map f)).range) hy⟩

/-- 概要：元の余核構造射は恒等構造射を保つ。
方針：対象の余核類で元の S の恒等則を照合する。
規約：準同型そのものの等号。
使われ方：余核図式の恒等則。 -/
lemma completionKZeroCokernelStructureMap_id (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    completionKZeroCokernelStructureMap r (𝟙 ι) f = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro z
  obtain ⟨y, rfl⟩ := completionKZeroVertexClass_surjective r ι f z
  have hy := congrArg (fun q : ((multiSEndofunctor r).obj ι) ⟶
      ((multiSEndofunctor r).obj ι) => (q.app Y).val.app (Opposite.op ⦋0⦌) y)
    ((multiSEndofunctor r).map_id ι)
  exact (completionKZeroCokernelStructureMap_vertex r (𝟙 ι) f y).trans
    (congrArg (completionKZeroVertexClass r ι f) hy)

/-- 概要：元の余核構造射は全 S 構造射の合成を保つ。
方針：対象の余核類で元の S の合成則を照合する。
規約：同じ元の構造射の合成を使う。
使われ方：余核図式の合成則。 -/
lemma completionKZeroCokernelStructureMap_comp (r : ℕ)
    {ι κ μ : Fin r → SimplexCategoryᵒᵖ} (α : ι ⟶ κ) (β : κ ⟶ μ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    completionKZeroCokernelStructureMap r (α ≫ β) f =
      (completionKZeroCokernelStructureMap r β f).comp
        (completionKZeroCokernelStructureMap r α f) := by
  apply AddMonoidHom.ext
  intro z
  obtain ⟨y, rfl⟩ := completionKZeroVertexClass_surjective r ι f z
  have hy := congrArg (fun q : ((multiSEndofunctor r).obj ι) ⟶
      ((multiSEndofunctor r).obj μ) => (q.app Y).val.app (Opposite.op ⦋0⦌) y)
    ((multiSEndofunctor r).map_comp α β)
  have hright := (congrArg (completionKZeroCokernelStructureMap r β f)
    (completionKZeroCokernelStructureMap_vertex r α f y)).trans
    (completionKZeroCokernelStructureMap_vertex r β f
      ((((multiSEndofunctor r).map α).app Y).val.app (Opposite.op ⦋0⦌) y))
  exact (completionKZeroCokernelStructureMap_vertex r (α ≫ β) f y).trans
    ((congrArg (completionKZeroVertexClass r μ f) hy).trans hright.symm)

/-- 概要：元の K₀ 余核の全 S 多単体的な可換群値図式。
方針：元の構造射と検証済みの恒等・合成則を束ねる。
規約：完備化証拠を図式の構成自体には要求しない。
使われ方：障害群の bar 型の面・退化との照合。 -/
def completionKZeroCokernelDiagram (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (Fin r → SimplexCategoryᵒᵖ) ⥤ AddCommGrpCat.{u} where
  obj ι := AddCommGrpCat.of (completionKZeroCokernel r ι f)
  map α := AddCommGrpCat.ofHom (completionKZeroCokernelStructureMap r α f)
  map_id ι := congrArg AddCommGrpCat.ofHom (completionKZeroCokernelStructureMap_id r ι f)
  map_comp α β := congrArg AddCommGrpCat.ofHom
    (completionKZeroCokernelStructureMap_comp r α β f)

end SerrePositivity.KST.SConstruction.Cofinality
