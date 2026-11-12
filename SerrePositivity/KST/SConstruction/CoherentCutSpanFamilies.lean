module
public import SerrePositivity.KST.SConstruction.CoherentPathMappingHomotopy
public import SerrePositivity.KST.SConstruction.FixedKanSpanFamilies

/-! # 元の二切断円柱の共通 Path パラメータでの相対合成
概要：一つの元の豊穣単体の二切断円柱を同じ全 Path 族上で合成する。
方針：両切断点を通る合成面の共通部分で両円柱が固定することから境界三角形を構成する。
規約：元の二円柱を保持し、境界の三角形や恒等性を追加仮定にしない。
使われ方：元の K prism の高次合成を、既存 BF 境界を保つ相対族へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {J : Type u} [LinearOrder J] {a b c d : J}
  {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 両方の指定切断点を通る、元の全 Path 族の共通合成面。 -/
def coherentDoubleCutBoundary (a b c d : J) : (nerve (Path a c)).Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough b ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough d

/-- 共通合成面では、第一の切断円柱は全時刻で元の豊穣作用を保つ。 -/
lemma coherentDoubleCutHomotopy_left_relative
    (s : EnrichedFunctor SSet.{u} (SimplicialThickening J) C)
    (hab : a ≤ b) (hbc : b ≤ c) :
    ((coherentDoubleCutBoundary a b c d).ι ▷ (Δ[1] : SSet.{u})) ≫
        (coherentPathMappingCutHomotopy s hab hbc).h =
      fst (coherentDoubleCutBoundary a b c d : SSet.{u}) Δ[1] ≫
        (coherentDoubleCutBoundary a b c d).ι ≫ s.map (.mk a) (.mk c) := by
  have h := fixedHomotopySpanBoundary_precomp
    (SSet.Subcomplex.homOfLE (show coherentDoubleCutBoundary a b c d ≤
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough b from inf_le_left)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough b).ι
    (coherentPathMappingCutHomotopy s hab hbc)
    (coherentPathMappingCutHomotopy_relative s hab hbc)
  simpa only [SSet.Subcomplex.homOfLE_ι] using h

/-- 共通合成面では、第二の切断円柱も全時刻で同じ元の豊穣作用を保つ。 -/
lemma coherentDoubleCutHomotopy_right_relative
    (s : EnrichedFunctor SSet.{u} (SimplicialThickening J) C)
    (had : a ≤ d) (hdc : d ≤ c) :
    ((coherentDoubleCutBoundary a b c d).ι ▷ (Δ[1] : SSet.{u})) ≫
        (coherentPathMappingCutHomotopy s had hdc).h =
      fst (coherentDoubleCutBoundary a b c d : SSet.{u}) Δ[1] ≫
        (coherentDoubleCutBoundary a b c d).ι ≫ s.map (.mk a) (.mk c) := by
  have h := fixedHomotopySpanBoundary_precomp
    (SSet.Subcomplex.homOfLE (show coherentDoubleCutBoundary a b c d ≤
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough d from inf_le_right)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough d).ι
    (coherentPathMappingCutHomotopy s had hdc)
    (coherentPathMappingCutHomotopy_relative s had hdc)
  simpa only [SSet.Subcomplex.homOfLE_ι] using h

/-- 二つの元の切断円柱を、共通合成面の指定三角形を自動構成して相対合成する。 -/
def coherentCutSpanComposite
    (s : EnrichedFunctor SSet.{u} (SimplicialThickening J) C)
    [KanComplex (SimplicialCategory.sHom (s.obj (.mk a)) (s.obj (.mk c)))]
    (hab : a ≤ b) (hbc : b ≤ c) (had : a ≤ d) (hdc : d ≤ c) :=
  fixedKanHomotopySpanComposite (coherentDoubleCutBoundary a b c d).ι
    (coherentPathMappingCutHomotopy s hab hbc) (coherentPathMappingCutHomotopy s had hdc)
    (coherentDoubleCutHomotopy_left_relative s hab hbc)
    (coherentDoubleCutHomotopy_right_relative s had hdc)

/-- 構成した全 Path 族の合成は、両切断点を通る元の合成面を全時刻で固定する。 -/
lemma coherentCutSpanComposite_relative
    (s : EnrichedFunctor SSet.{u} (SimplicialThickening J) C)
    [KanComplex (SimplicialCategory.sHom (s.obj (.mk a)) (s.obj (.mk c)))]
    (hab : a ≤ b) (hbc : b ≤ c) (had : a ≤ d) (hdc : d ≤ c) :
    ((coherentDoubleCutBoundary a b c d).ι ▷ (Δ[1] : SSet.{u})) ≫
        (coherentCutSpanComposite s hab hbc had hdc).h =
      fst (coherentDoubleCutBoundary a b c d : SSet.{u}) Δ[1] ≫
        (coherentDoubleCutBoundary a b c d).ι ≫
          (coherentPathCutSplit hab hbc ≫
            (s.map (.mk a) (.mk b) ⊗ₘ s.map (.mk b) (.mk c)) ≫
              eComp SSet (s.obj (.mk a)) (s.obj (.mk b)) (s.obj (.mk c))) :=
  fixedKanHomotopySpanComposite_relative _ _ _ _ _

/-- 共通合成面では、構成した合成は元の単体の豊穣作用そのものを固定する。 -/
lemma coherentCutSpanComposite_relative_original
    (s : EnrichedFunctor SSet.{u} (SimplicialThickening J) C)
    [KanComplex (SimplicialCategory.sHom (s.obj (.mk a)) (s.obj (.mk c)))]
    (hab : a ≤ b) (hbc : b ≤ c) (had : a ≤ d) (hdc : d ≤ c) :
    ((coherentDoubleCutBoundary a b c d).ι ▷ (Δ[1] : SSet.{u})) ≫
        (coherentCutSpanComposite s hab hbc had hdc).h =
      fst (coherentDoubleCutBoundary a b c d : SSet.{u}) Δ[1] ≫
        (coherentDoubleCutBoundary a b c d).ι ≫ s.map (.mk a) (.mk c) :=
  fixedKanHomotopySpanComposite_relative_source _ _ _ _ _

end SerrePositivity.KST.SConstruction
