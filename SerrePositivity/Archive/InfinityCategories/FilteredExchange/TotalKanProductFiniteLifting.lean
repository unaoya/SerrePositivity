module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.TotalKanProductComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SimultaneousTotalDetection

/-!
概要：一般 filtered な底上で、全空間 Kan 模型の積への任意の有限射を比較写像から持ち上げる。
方針：二射影を共通頂点の元の二 fiber で同時に表示し、元の引き戻しへまとめる。
規約：元の有限射への実際のホモトピーを返す。
使われ方：有限積比較の弱同値性の全有限試験射による検証の全射側。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：積への元の有限射は、同じ底の fiber ごとの積の全空間模型を通る射にホモトピック。
方針：二つの有限射を同じ頂点へ移し、引き戻しへの指定持ち上げと二つのホモトピーを組にする。
規約：全有限単体集合を検査する。比較の単射側・相対境界の検出は別途必要。 -/
lemma totalKanProductComparison_finite_lifting {K E D B : SSet.{u}}
    [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : E ⟶ B) [LeftFibration p] (q : D ⟶ B) [LeftFibration q]
    (f : K ⟶ continuousKanReplacement.obj E ⊗ continuousKanReplacement.obj D) :
    ∃ g : K ⟶ continuousKanReplacement.obj (pullback p q),
      Nonempty (SSet.Homotopy f (g ≫ totalKanProductComparison p q)) := by
  obtain ⟨b, s, t, ⟨Hs⟩, ⟨Ht⟩⟩ := continuousKanLeftFibration_pair_finite_fiber_detection p q
    (f ≫ fst (continuousKanReplacement.obj E) (continuousKanReplacement.obj D))
    (f ≫ snd (continuousKanReplacement.obj E) (continuousKanReplacement.obj D))
  let g := fiberPairToPullback p q b s t ≫ continuousKanReplacementUnit.app (pullback p q)
  have hg : g ≫ totalKanProductComparison p q =
      lift (s ≫ vertexFiberι p b ≫ continuousKanReplacementUnit.app E)
        (t ≫ vertexFiberι q b ≫ continuousKanReplacementUnit.app D) :=
    fiberPairToPullback_comparison p q b s t
  refine ⟨g, ⟨⟨lift Hs.h Ht.h, ?_, ?_, ?_⟩⟩⟩
  · change SSet.ι₀ ≫ lift Hs.h Ht.h = f
    rw [comp_lift, Hs.h₀, Ht.h₀]
    apply CartesianMonoidalCategory.hom_ext <;> simp only [lift_fst, lift_snd]
  · change SSet.ι₁ ≫ lift Hs.h Ht.h = g ≫ totalKanProductComparison p q
    rw [comp_lift, Hs.h₁, Ht.h₁]
    exact hg.symm
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：有限試験対象からの写像空間の連結成分で、積の比較は全射。
方針：任意の成分の頂点を射に戻し、実際の有限持ち上げのホモトピーを使う。
規約：全有限形状。使われ方：有限積比較の弱同値性の全射側の検証。 -/
lemma totalKanProductComparison_mapPiZero_surjective {K E D B : SSet.{u}}
    [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : E ⟶ B) [LeftFibration p] (q : D ⟶ B) [LeftFibration q] :
    Function.Surjective (SSet.mapπ₀ ((ihom K).map (totalKanProductComparison p q))) := by
  intro a
  obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective a
  obtain ⟨f, rfl⟩ := (functorVertexEquiv K _).surjective v
  obtain ⟨g, ⟨H⟩⟩ := totalKanProductComparison_finite_lifting p q f
  refine ⟨SSet.π₀.mk (functorVertex g), ?_⟩
  change SSet.π₀.mk (functorVertex (g ≫ totalKanProductComparison p q)) =
    SSet.π₀.mk (functorVertex f)
  exact (SSet.π₀.sound
    (SSet.Edge.ofTruncated (functorEdgeOfSimplicialHomotopy H))).symm

end SerrePositivity.InfinityCategories.F2
