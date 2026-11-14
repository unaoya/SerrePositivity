module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LiftedStandardSimplexHomEvaluation

/-!
# 指定積重みHom同型を同じ自由随伴でuncurryする

概要：A09の積重み側の全標準単体を、元の自由鎖随伴の自然変換へ戻す。
方針：指定標準単体Yoneda評価と合成随伴の余単位則を使う。
規約：既存構成の法則。重み・パラメータ・全図式射を保持する。
使われ方：HA 1.2.4、IS-W2 B02の指定AW比較と実合成の全単体照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (A : Type u) [CommRing A] {J : Type u} [SmallCategory J]

/-- 概要：既存の重み付き切断と自由鎖の合成随伴は同じ自然変換にuncurryする。
方針：同じ随伴のHom合成と元のlift/uncurry則。
規約：任意のパラメータ。使われ方：HA 1.2.4 の積重み側の指定射の照合。 -/
theorem weightedFreeChainsAdjunction_uncurry (W : J ⥤ SSet.{u})
    (Y : SSet.{u}) (Q : J ⥤ Complex A)
    (f : freeNegativeChainsDiagram (A := A) (W ⊗ (Functor.const J).obj Y) ⟶ Q) :
    weightedSectionsUncurry
      (((weightedSectionsAdjunction W).comp (freeNegativeChainsDiagramAdjunction A J)).homEquiv
        Y Q f) =
    (freeNegativeChainsDiagramAdjunction A J).homEquiv (W ⊗ (Functor.const J).obj Y) Q f := by
  have hl (H : J ⥤ SSet.{u}) (s : W ⊗ (Functor.const J).obj Y ⟶ H) :
      weightedSectionsUncurry ((weightedSectionsAdjunction W).homEquiv Y H s) = s := by
    simp only [weightedSectionsAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
    exact weightedSectionsUncurry_lift s
  simp only [Adjunction.comp_homEquiv]
  exact hl _ _

/-- 概要：A09の指定積重みHom同型を全標準単体で戻すと同じ自由随伴になる。
方針：元のYoneda射と合成随伴のuncurry則を合成する。
規約：標準単体の宇宙同型も指定どおり。使われ方：HA 1.2.4 の元の比較射の成分。 -/
theorem freeProductSectionsHomIso_uncurry (W : J ⥤ SSet.{u}) (Q : J ⥤ Complex A)
    (n : SimplexCategory) (f : (freeProductFrame A W (liftedStandardSimplexParameter J)).obj n ⟶ Q) :
    weightedSectionsUncurry
      (liftedStandardSimplexIso.{u}.hom.app n ≫ SSet.yonedaEquiv.symm
        ((freeProductSectionsHomIso A W Q).hom.app (Opposite.op n) f)) =
    (freeNegativeChainsDiagramAdjunction A J).homEquiv
      (W ⊗ (Functor.const J).obj
        ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n))) Q f := by
  let h := ((weightedSectionsAdjunction W).comp (freeNegativeChainsDiagramAdjunction A J)).homEquiv
    ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)) Q f
  have he : (freeProductSectionsHomIso A W Q).hom.app (Opposite.op n) f =
      (liftedStandardSimplexHomIso (weightedSections W (Q ⋙ truncatedDoldKanFunctor A))).hom.app
        (Opposite.op n) h := rfl
  rw [he, liftedStandardSimplexHomIso_yoneda]
  exact weightedFreeChainsAdjunction_uncurry A W _ Q f

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
