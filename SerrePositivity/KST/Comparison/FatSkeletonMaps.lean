module

public import SerrePositivity.KST.Comparison.FatSkeleton
public import SerrePositivity.KST.Comparison.FatNormalFormMap

/-!
# fat realization の有限骨格の構造写像

概要：各行の骨格への因子化と、二重単体集合の射が誘導する骨格の射を構成する。
方針：各行の像の次元の上限と、標準形の自然性を使う。
規約：Segal 1974 Proposition 1.6 の有限骨格の図式。
使われ方：骨格の付着の四角形と自然な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial

/--
概要：n 行と標準 n 単体の積から n 骨格への射。
方針：各行の包含の像が n 骨格に含まれることを使う。
規約：構成後の包含との合成は元の行の包含そのもの。
使われ方：有限骨格の新しい単体の付着。
-/
def fatSkeletonRow (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    F.obj (op ⦋n⦌) ⊗ Δ[n] ⟶ (fatSkeleton F n : SSet.{u}) :=
  SSet.Subcomplex.lift (fatRealizationInclusion F n) (by
    rintro d y ⟨⟨x, t⟩, rfl⟩
    exact fatRealizationInclusion_mem_skeleton F n d x t)

/--
概要：各行の骨格への射を全体へ含めると元の包含になる。
方針：部分単体集合への lift の定義を計算する。
規約：自然性の四角形の上端の計算。
使われ方：付着の図式の可換性。
-/
@[reassoc] theorem fatSkeletonRow_ι (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    fatSkeletonRow F n ≫ (fatSkeleton F n).ι = fatRealizationInclusion F n := rfl

/--
概要：二重単体集合の射が誘導する有限骨格の射。
方針：標準形の写像が次数を保つことから全体の射を骨格へ制限する。
規約：骨格の番号は変えない。
使われ方：骨格ごとの比較の自然性。
-/
def fatSkeletonMap {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (α : F ⟶ G) (n : ℕ) :
    (fatSkeleton F n : SSet.{u}) ⟶ (fatSkeleton G n : SSet.{u}) :=
  SSet.Subcomplex.lift ((fatSkeleton F n).ι ≫ fatRealizationMap α) (by
    rintro d y ⟨x, rfl⟩
    change (fatDegreeNormalize G d ((fatRealizationMap α).app d x.1)).degree.len ≤ n
    rw [fatDegreeNormalize_map]
    exact x.2)

/--
概要：骨格の射は全体への包含と可換である。
方針：部分単体集合への lift の計算則を使う。
規約：元の fat realization の射と比較する向き。
使われ方：骨格の余極限の比較。
-/
@[reassoc] theorem fatSkeletonMap_ι {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    (α : F ⟶ G) (n : ℕ) :
    fatSkeletonMap α n ≫ (fatSkeleton G n).ι =
      (fatSkeleton F n).ι ≫ fatRealizationMap α := rfl

/--
概要：固定した次数の fat realization の骨格を取る関手。
方針：恒等と合成は全体の関手の式を各次数の部分型へ制限する。
規約：射の自然性は標準形の自然性から得る。
使われ方：有限骨格の帰納を元の図式の射に関して自然にする。
-/
def fatSkeletonFunctor (n : ℕ) : (SimplexCategoryᵒᵖ ⥤ SSet.{u}) ⥤ SSet.{u} where
  obj F := fatSkeleton F n
  map α := fatSkeletonMap α n
  map_id F := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f => f.app d x.1) (fatRealizationFunctor.map_id F)
  map_comp α β := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f => f.app d x.1) (fatRealizationFunctor.map_comp α β)

/--
概要：各有限骨格の全体への包含は自然変換をなす。
方針：骨格の射の包含との可換性を使う。
規約：終域は実際の fat realization の関手。
使われ方：有限骨格と無限骨格の四角形の比較。
-/
def fatSkeletonInclusion (n : ℕ) : fatSkeletonFunctor.{u} n ⟶ fatRealizationFunctor where
  app F := (fatSkeleton F n).ι
  naturality {_ _} _ := rfl

end SerrePositivity.KST.Comparison
