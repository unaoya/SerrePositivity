module

public import SerrePositivity.KST.Comparison.RegularBarPathComparison
public import SerrePositivity.KST.Comparison.RegularBarLoop
public import SerrePositivity.KST.Comparison.LoopPathPullback

/-!
# 標準群完備化写像と path のファイバー比較の一致

概要：既存の標準ループ写像を path space へ含めると、正則 bar の収縮からの比較に一致する。
方針：内部 Hom の包含後に uncurry し、区間上の標準辺写像の既存の式を使う。
規約：Segal 1974 Proposition 1.5、KST Lemma 2.13。比較射を別の選択で置き換えない。
使われ方：ホモトピーファイバーの定理から標準写像そのものの局所化可逆性を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory MonoidalClosed BraidedCategory
open scoped Simplicial
open SerrePositivity.SimplicialModel

/--
概要：標準群完備化写像と正則 bar からの path の比較は、loop の包含後に一致する。
方針：両辺を区間上で評価し、収縮の射影が標準辺写像となる計算を使う。
規約：群状性や Kan 性はこの写像の一致には不要。
使われ方：標準群完備化写像の局所化可逆性の判定。
-/
theorem monoidGroupCompletionMap_path (M : SimplicialObject MonCat.{u}) :
    monoidGroupCompletionMap M ≫ loopPathRestriction (monoidBarKanPointed M) =
      regularBarFiberMap M ≫ regularBarPathMap M := by
  let Y := monoidBarKanPointed M
  let q := AnodyneKanReplacement.unit.app (monoidBar M)
  let h := (β_ (Δ[1] : SSet.{u}) (monoidSpace M)).hom ≫ monoidBarEdgeMap M ≫ q
  have hL : monoidGroupCompletionMap M ≫ loopPathRestriction Y ≫
      PointedObject.basedHomι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y = curry h := by
    rw [loopPathRestriction_ι]
    apply uncurry_injective
    rw [← Category.assoc, uncurry_pre_app, uncurry_curry]
    exact monoidGroupCompletionMap_evaluation M
  have hR : regularBarFiberMap M ≫ regularBarPathMap M ≫
      PointedObject.basedHomι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y = curry h := by
    rw [regularBarPathMap, basedPathFamilyMap_ι, ← curry_natural_left]
    congr 1
    have hb : (Δ[1] : SSet.{u}) ◁ regularBarFiberMap M ≫
        (β_ (Δ[1] : SSet.{u}) (regularBar M)).hom =
        (β_ (Δ[1] : SSet.{u}) (monoidSpace M)).hom ≫
          regularBarFiberMap M ▷ (Δ[1] : SSet.{u}) := braiding_naturality_right _ _
    change (Δ[1] : SSet.{u}) ◁ regularBarFiberMap M ≫
      ((β_ (Δ[1] : SSet.{u}) (regularBar M)).hom ≫
        (regularBarContractionMap M ≫ regularBarProjection M ≫ q)) = h
    rw [← Category.assoc, hb, Category.assoc]
    change (β_ (Δ[1] : SSet.{u}) (monoidSpace M)).hom ≫
      (regularBarFiberMap M ▷ (Δ[1] : SSet.{u}) ≫
        regularBarContractionMap M ≫ regularBarProjection M) ≫ q = h
    rw [regularBarContraction_projection]
  apply (cancel_mono (PointedObject.basedHomι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y)).mp
  simpa only [Category.assoc] using hL.trans hR.symm

end SerrePositivity.KST.Comparison
