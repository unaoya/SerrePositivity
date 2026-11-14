module
public import SerrePositivity.KST.SConstruction.Cofinality.KZeroToWideGroup

/-!
概要：元の wide 成分と元の三角圏 K₀ 余核を可換群として同定する。
方針：K₀ の普遍性で得た逆射を元の頂点類で計算し、全射性と合わせる。
規約：共終性の主定理や K₀ 単射性を仮定しない。
使われ方：相対実現の離散的障害を元の K₀ 商群へ同定する。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory Limits Pretriangulated SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の対象の wide 成分は同じ対象の K₀ 余核類へ写る。
方針：対象を実頂点表示へ戻して降下の定義を計算する。
規約：同じ対象類を保持する。
使われ方：障害写像の加法性と合成の計算。 -/
lemma completionWideKZeroObstruction_objectClass (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (a : hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier) :
    completionWideKZeroObstruction r ι f (completionWideObjectClass r ι f hf a) =
      (QuotientAddGroup.mk' (triangulatedKZeroSourceMap
        (((multiSEndofunctor r).obj ι).map f)).range) (TriangulatedK0.mk a) := by
  obtain ⟨a, rfl⟩ := Truncated.HomotopyCategory.mk_surjective a
  rfl

/-- 概要：K₀ 余核からの比較は元の成分比較の左逆。
方針：全成分を元の頂点で表し、二回の降下を生成元で計算する。
規約：比較射は構成済みの元の障害写像そのもの。
使われ方：障害写像の単射性。 -/
lemma completionKZeroCokernelToWide_leftInverse (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    Function.LeftInverse (completionKZeroCokernelToWide r ι f hf)
      (completionWideKZeroObstruction r ι f) := by
  intro a
  obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective a
  exact completionKZeroToWide_mk r ι f hf (HomotopyCategory.mk a.val)

/-- 概要：元の成分から元の K₀ 余核への比較は全単射。
方針：構成した左逆の単射性と、対象表示による既存の全射性を合わせる。
規約：K₀ の単射性そのものとは区別する。
使われ方：離散的障害の集合としての同定。 -/
theorem completionWideKZeroObstruction_bijective (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    Function.Bijective (completionWideKZeroObstruction r ι f) :=
  ⟨(completionKZeroCokernelToWide_leftInverse r ι f hf).injective,
    completionWideKZeroObstruction_surjective r ι f hf⟩

/-- 概要：元の成分評価を加法準同型として束ねる。
方針：零成分の像を消し、双積の完全三角形の K₀ 関係を余核へ写す。
規約：順方向は元の障害写像を変更しない。
使われ方：障害の可換群としての同定。 -/
def completionWideKZeroObstructionHom (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    completionWideGroup r ι f hf →+ completionKZeroCokernel r ι f where
  toFun := completionWideKZeroObstruction r ι f
  map_zero' := completionKZeroVertexClass_zero_of_image r ι f _
    ((completionImageClosedPredicate r ι f hf).zero_mem
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex (((multiSEndofunctor r).obj ι).obj Y).carrier).isZero)
  map_add' a b := by
    obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective a
    obtain ⟨b, rfl⟩ := SSet.π₀.mk_surjective b
    let C := hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier
    let A : C := HomotopyCategory.mk a.val
    let B : C := HomotopyCategory.mk b.val
    let π := QuotientAddGroup.mk'
      (triangulatedKZeroSourceMap (((multiSEndofunctor r).obj ι).map f)).range
    have h := congrArg π (TriangulatedK0.mk_triangle (binaryBiproductTriangle A B)
      (binaryBiproductTriangle_distinguished A B))
    rw [map_add] at h
    exact (congrArg (completionWideKZeroObstruction r ι f)
      (completionWideAdd_objectClass r ι f hf A B)).trans
        ((completionWideKZeroObstruction_objectClass r ι f hf (A ⊞ B)).trans h)

/-- 概要：元の wide 成分群は元の三角圏 K₀ の余核と同型。
方針：元の障害準同型と実証明した全単射性を束ねる。
規約：全 S 多次数で元の指定射の余核を使う。
使われ方：相対 fiber 列の離散的障害の商群同定。 -/
def completionWideKZeroObstructionEquiv (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    completionWideGroup r ι f hf ≃+ completionKZeroCokernel r ι f :=
  AddEquiv.ofBijective (completionWideKZeroObstructionHom r ι f hf)
    (completionWideKZeroObstruction_bijective r ι f hf)

end SerrePositivity.KST.SConstruction.Cofinality
