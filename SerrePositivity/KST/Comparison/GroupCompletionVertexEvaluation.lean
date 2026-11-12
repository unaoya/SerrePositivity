module

public import SerrePositivity.KST.Comparison.GroupCompletionBasepoint
public import SerrePositivity.KST.Spectra.SphereSimplex
public import SerrePositivity.KST.Spectra.PointedMappingFamilyVertices

/-!
# 標準群完備化写像の頂点を区間で評価する

概要：群完備化写像の各頂点が表す円の写像を、元の bar の辺の区間評価へ戻す。
方針：零次パラメータの切断と curry の自然性で評価を交換する。
規約：Segal 1974 Proposition 1.5 の標準写像の実際の代表。
使われ方：KST Lemma 2.13 の基本群の積との整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory MonoidalClosed BraidedCategory SSet
open scoped Simplicial
open SerrePositivity.SimplicialModel

/--
概要：ループの族の一頂点の円からの写像を区間へ引き戻す。
方針：零次切断の自然性と指数の反変な制限を使う。
規約：標的の Kan 性は不要。
使われ方：円の写像を bar の辺の具体的な代表と比較する。
-/
theorem loopVertex_pullback {X : SSet.{u}} (Y : PointedSimplicialSet.{u})
    (f : X ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right) (x : X _⦋0⦌) :
    PointedObject.cofiberQuotient (boundary.{u} 1).ι ≫
        (Spectra.PointedMapping.familyMap PointedSimplicialSet.circle Y (f.app _ x)).right =
      Spectra.PointedMapping.zeroSection (Δ[1] : SSet.{u}) ≫
        uncurry (yonedaEquiv.symm x ≫ f ≫ loopPathRestriction Y ≫
          PointedObject.basedHomι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y) := by
  change _ ≫ (Spectra.PointedMapping.zeroSection _ ≫
    uncurry (yonedaEquiv.symm (f.app _ x) ≫ _)) = _
  rw [← yonedaEquiv_symm_comp, ← Category.assoc,
    Spectra.PointedMapping.zeroSection_natural, Category.assoc]
  congr 1
  rw [← uncurry_pre_app, Category.assoc, Category.assoc, loopPathRestriction_ι]

/--
概要：標準群完備化写像の一頂点の境界定数単体は bar の辺の区間評価である。
方針：頂点の引き戻しの式へ標準写像の区間評価と curry の自然性を適用する。
規約：元の零次モノイドの元 a に対応する実際の写像の式。
使われ方：nerve の一次単体・二次単体を基本群の乗法へ渡す。
-/
theorem groupCompletionVertex_simplex_map (M : SimplicialObject MonCat.{u})
    (a : (monoidSpace M) _⦋0⦌) :
    (Spectra.SphereSimplex.equiv (monoidBarKanPointed M) 1
      (Spectra.PointedMapping.familyMap PointedSimplicialSet.circle (monoidBarKanPointed M)
        ((monoidGroupCompletionMap M).app _ a))).map =
      Spectra.PointedMapping.zeroSection (Δ[1] : SSet.{u}) ≫
        (Δ[1] : SSet.{u}) ◁ yonedaEquiv.symm a ≫
          (β_ (Δ[1] : SSet.{u}) (monoidSpace M)).hom ≫ monoidBarEdgeMap M ≫
            AnodyneKanReplacement.unit.app (monoidBar M) := by
  calc
    _ = Spectra.PointedMapping.zeroSection (Δ[1] : SSet.{u}) ≫
        uncurry (yonedaEquiv.symm a ≫ monoidGroupCompletionMap M ≫
          loopPathRestriction (monoidBarKanPointed M) ≫
            PointedObject.basedHomι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval (monoidBarKanPointed M)) :=
      loopVertex_pullback (monoidBarKanPointed M) (monoidGroupCompletionMap M) a
    _ = _ := by
      rw [monoidGroupCompletionMap_restriction_ι, uncurry_natural_left, uncurry_curry]

end SerrePositivity.KST.Comparison
