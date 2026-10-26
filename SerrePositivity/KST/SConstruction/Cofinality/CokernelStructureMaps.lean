module
public import SerrePositivity.KST.SConstruction.Cofinality.WideKZeroObstructionEquiv
public import SerrePositivity.KST.SConstruction.TriangulatedKZeroNatIso

/-!
概要：元の K₀ 余核を全 S 多次数の構造射で結ぶ。
方針：元の f の厳密な自然性と K₀ の合成則で像の保存を証明する。
規約：同じ指定射の像で割り、別の商群へ置き換えない。
使われ方：離散的障害の全単体的 bar 同定。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：全 S 構造射の K₀ 作用は元の始域の K₀ 像を保つ。
方針：元の f の自然性へ K₀ の関手性を適用する。
規約：全多次数で同じ誘導準同型の像を使う。
使われ方：構造射の K₀ 余核への降下条件。 -/
lemma completionKZeroRange_map_le (r : ℕ) {ι κ : Fin r → SimplexCategoryᵒᵖ}
    (α : ι ⟶ κ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (triangulatedKZeroSourceMap (((multiSEndofunctor r).obj ι).map f)).range ≤
      ((triangulatedKZeroSourceMap (((multiSEndofunctor r).obj κ).map f)).range).comap
        (triangulatedKZeroSourceMap (((multiSEndofunctor r).map α).app Y)) := by
  have he := (triangulatedKZeroSourceMap_comp
    (((multiSEndofunctor r).obj ι).map f) (((multiSEndofunctor r).map α).app Y)).symm.trans
    ((congrArg triangulatedKZeroSourceMap (((multiSEndofunctor r).map α).naturality f)).trans
      (triangulatedKZeroSourceMap_comp (((multiSEndofunctor r).map α).app X)
        (((multiSEndofunctor r).obj κ).map f)))
  rintro _ ⟨a, rfl⟩
  refine ⟨triangulatedKZeroSourceMap (((multiSEndofunctor r).map α).app X) a, ?_⟩
  exact (DFunLike.congr_fun he a).symm

/-- 概要：同じ全多次数の構造射による K₀ 余核間の準同型。
方針：元の標的の K₀ 作用を像保存で余核へ降ろす。
規約：指定された元の構造射を使う。
使われ方：障害群の面・退化の実作用。 -/
def completionKZeroCokernelStructureMap (r : ℕ) {ι κ : Fin r → SimplexCategoryᵒᵖ}
    (α : ι ⟶ κ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    completionKZeroCokernel r ι f →+ completionKZeroCokernel r κ f :=
  QuotientAddGroup.map (triangulatedKZeroSourceMap (((multiSEndofunctor r).obj ι).map f)).range
    (triangulatedKZeroSourceMap (((multiSEndofunctor r).obj κ).map f)).range
    (triangulatedKZeroSourceMap (((multiSEndofunctor r).map α).app Y))
    (completionKZeroRange_map_le r α f)

/-- 概要：余核の構造射は元の各対象の余核類で標的の構造射を回収する。
方針：商の生成元公式と元の K₀ 射の対象類公式を合成する。
規約：同じ元の頂点を評価する。
使われ方：wide 成分比較の全多次数自然性。 -/
lemma completionKZeroCokernelStructureMap_vertex (r : ℕ)
    {ι κ : Fin r → SimplexCategoryᵒᵖ} (α : ι ⟶ κ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (y : (((multiSEndofunctor r).obj ι).obj Y).carrier _⦋0⦌) :
    completionKZeroCokernelStructureMap r α f (completionKZeroVertexClass r ι f y) =
      completionKZeroVertexClass r κ f
        ((((multiSEndofunctor r).map α).app Y).val.app (Opposite.op ⦋0⦌) y) :=
  congrArg (QuotientAddGroup.mk'
    (triangulatedKZeroSourceMap (((multiSEndofunctor r).obj κ).map f)).range)
    (triangulatedKZeroSourceMap_mk (((multiSEndofunctor r).map α).app Y)
      (HomotopyCategory.mk y))

end SerrePositivity.KST.SConstruction.Cofinality
