module
public import SerrePositivity.KST.SConstruction.Cofinality.CokernelStructureMaps
public import SerrePositivity.KST.SConstruction.Cofinality.WideStageMaps

/-!
概要：元の具体的 wide 模型と K₀ 余核の比較の全 S 多次数自然性を示す。
方針：供給模型の等号で元の構造射を移し、対象類上の余核作用と照合する。
規約：選択した供給の自然性を仮定せず、元の構造射の作用を保持する。
使われ方：障害群を全単体的 bar 図式として照合する入口。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：全 S 構造射を元の具体的 wide 模型の間で実現する。
方針：選択された模型への等号と既存の元の wide 構造射を合成する。
規約：包含後の単体の値は元の S 構造射の値である。
使われ方：元の wide 成分の全多次数作用。 -/
def completionCanonicalWideStructureMap (r : ℕ)
    {ι κ : Fin r → SimplexCategoryᵒᵖ} (α : ι ⟶ κ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}) ⟶
      (LocalizingInvariants.completionCofiberWide
        (((multiSEndofunctor r).obj κ).map f).val : SSet.{u}) :=
  Subcomplex.homOfLE (completionMultiWide_eq r ι f hf).symm.le ≫
    multiWideStageMap stableWideCofinalitySupply r α f hf ≫
      Subcomplex.homOfLE (completionMultiWide_eq r κ f hf).le

/-- 概要：元の wide 成分と K₀ 余核の比較は全 S 構造射と可換。
方針：成分を実頂点で表示し、元の余核の対象類公式を使う。
規約：元の wide 構造射による成分写像そのものを照合する。
使われ方：商群同定の全多単体自然性。 -/
lemma completionCanonicalWideStructureMap_obstruction (r : ℕ)
    {ι κ : Fin r → SimplexCategoryᵒᵖ} (α : ι ⟶ κ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (a : SSet.π₀ (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u})) :
    completionWideKZeroObstruction r κ f
        (SSet.mapπ₀ (completionCanonicalWideStructureMap r α f hf) a) =
      completionKZeroCokernelStructureMap r α f (completionWideKZeroObstruction r ι f a) := by
  obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective a
  exact (completionKZeroCokernelStructureMap_vertex r α f a.val).symm

/-- 概要：元の全 S 構造射の成分作用を加法準同型として束ねる。
方針：元の商群同型の間に K₀ 余核の構造射を挟む。
規約：次の公式で元の成分写像との一致を検証する。
使われ方：離散的障害の可換群値図式。 -/
def completionWideGroupStructureMap (r : ℕ)
    {ι κ : Fin r → SimplexCategoryᵒᵖ} (α : ι ⟶ κ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    completionWideGroup r ι f hf →+ completionWideGroup r κ f hf :=
  (completionWideKZeroObstructionEquiv r κ f hf).symm.toAddMonoidHom.comp
    ((completionKZeroCokernelStructureMap r α f).comp
      (completionWideKZeroObstructionEquiv r ι f hf).toAddMonoidHom)

/-- 概要：構成した障害群の構造射は元の wide 成分写像そのものである。
方針：標的の元の商群同型で検査し、成分比較の自然性を使う。
規約：別の作用へ置き換えず元の S 構造射を回収する。
使われ方：群値図式と元の相対旗図式の接続。 -/
lemma completionWideGroupStructureMap_apply (r : ℕ)
    {ι κ : Fin r → SimplexCategoryᵒᵖ} (α : ι ⟶ κ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (a : completionWideGroup r ι f hf) :
    completionWideGroupStructureMap r α f hf a =
      SSet.mapπ₀ (completionCanonicalWideStructureMap r α f hf) a := by
  apply (completionWideKZeroObstructionEquiv r κ f hf).injective
  exact ((completionWideKZeroObstructionEquiv r κ f hf).apply_symm_apply _).trans
    (completionCanonicalWideStructureMap_obstruction r α f hf a).symm

end SerrePositivity.KST.SConstruction.Cofinality
