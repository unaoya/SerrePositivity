module
public import SerrePositivity.KST.SConstruction.Cofinality.WideTriangleAdditivity

/-!
概要：元の同じ三角圏 K₀ から元の wide 成分の可換群へ写す。
方針：対象の成分評価の同型不変性と三角形の加法関係を K₀ の普遍性へ渡す。
規約：群構造は構成済みの明示的データで、追加の供給仮定を入れない。
使われ方：K₀ 余核と離散的障害の群同定の逆方向。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の wide 成分の明示的な可換群を束ねる。
方針：構成済みの群構造を bundled な可換群へ包む。
規約：底の型は同じ元の wide 模型の成分集合。
使われ方：加法準同型の標的として使う群。 -/
def completionWideGroup (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) : AddCommGrpCat.{u} := by
  let : AddCommGroup (SSet.π₀ (LocalizingInvariants.completionCofiberWide
    (((multiSEndofunctor r).obj ι).map f).val : SSet.{u})) := completionWideAddCommGroup r ι f hf
  exact AddCommGrpCat.of (SSet.π₀ (LocalizingInvariants.completionCofiberWide
    (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}))

/-- 概要：元の三角圏 K₀ の対象類を同じ wide 成分へ送る加法準同型。
方針：同型と完全三角形の関係で成分評価を降ろす。
規約：元の指定射の同じ S 多次数を保持する。
使われ方：余核から障害群への逆写像の前段。 -/
def completionKZeroToWide (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    TriangulatedK0 (hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier) →+
      completionWideGroup r ι f hf :=
  TriangulatedK0.lift (completionWideObjectClass r ι f hf)
    (fun e => completionWideObjectClass_iso r ι f hf e)
    (fun T hT => completionWideTriangle_additivity r ι f hf T hT)

/-- 概要：K₀ からの成分評価は元の各対象類で成分そのものを返す。
方針：K₀ の降下の生成元公式を使う。
規約：指定した対象評価を保持する。
使われ方：余核の逆写像の合成の計算。 -/
lemma completionKZeroToWide_mk (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (a : hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier) :
    completionKZeroToWide r ι f hf (TriangulatedK0.mk a) =
      completionWideObjectClass r ι f hf a :=
  TriangulatedK0.lift_mk _ _ _ a

/-- 概要：元の始域 K₀ の像は wide 成分の零元へ写る。
方針：対象類上で元の誘導写像を計算し、本質像の零成分判定を適用する。
規約：K₀ の単射性を仮定しない。
使われ方：成分評価を元の K₀ 余核へ降ろす核条件。 -/
lemma completionKZeroToWide_comp_source (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    (completionKZeroToWide r ι f hf).comp
      (triangulatedKZeroSourceMap (((multiSEndofunctor r).obj ι).map f)) = 0 := by
  apply TriangulatedK0.hom_ext
  intro a
  obtain ⟨a, rfl⟩ := Truncated.HomotopyCategory.mk_surjective a
  change completionKZeroToWide r ι f hf
    (triangulatedKZeroSourceMap (((multiSEndofunctor r).obj ι).map f)
      (TriangulatedK0.mk (HomotopyCategory.mk a))) = 0
  rw [triangulatedKZeroSourceMap_mk, completionKZeroToWide_mk]
  exact completionWideObjectClass_zero_of_image r ι f hf _ ⟨a, ⟨Iso.refl _⟩⟩

/-- 概要：元の K₀ の余核から元の wide 成分群への逆方向の比較。
方針：元の始域 K₀ を零化する成分評価を余核へ降ろす。
規約：全単射性を入力にせず、元の準同型の像で割る。
使われ方：離散的障害と K₀ 余核の同定。 -/
def completionKZeroCokernelToWide (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    completionKZeroCokernel r ι f →+ completionWideGroup r ι f hf :=
  QuotientAddGroup.lift (triangulatedKZeroSourceMap (((multiSEndofunctor r).obj ι).map f)).range
    (completionKZeroToWide r ι f hf) (by
      rintro _ ⟨a, rfl⟩
      exact DFunLike.congr_fun (completionKZeroToWide_comp_source r ι f hf) a)

end SerrePositivity.KST.SConstruction.Cofinality
