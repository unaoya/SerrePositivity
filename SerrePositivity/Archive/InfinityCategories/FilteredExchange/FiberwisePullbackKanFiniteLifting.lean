module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberwisePullbackOriginalInputDetection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanCospanPointRecognition
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalPullbackInputTransport
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SimultaneousTotalDetection

/-!
概要：任意の有限 Kan 引き戻し射を、元の一値の引き戻しの実際の比較像で検出する。
方針：二入力を元の全空間へ輸送し、指定 path を保持した同時検出を合成する。
規約：一般の coherent 図式の元の三全空間と構成済み比較を扱う。
使われ方：一般 coherent filtered 引き戻し比較の全射側。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：任意の有限標的射は元の一値の引き戻しの実際の比較像へホモトピック。
方針：二入力の同時検出を二入力射に沿って持ち上げ、元の二入力の場合へ帰着する。
規約：strict な図式への置換は不要。使われ方：一般 coherent 引き戻し比較の有限全射性。 -/
lemma fiberwisePullbackKanComparison_finite_value_detection {K E D H B : SSet.{u}}
    [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
    [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)]
    (a : K ⟶ intervalPullback (continuousKanReplacement.map f) (continuousKanReplacement.map g)) :
    ∃ b : B _⦋0⦌, ∃ v : K ⟶ intervalPullback (vertexFiberMap (f ≫ p) p f rfl b)
      (vertexFiberMap (g ≫ p) p g rfl b),
      Nonempty (SSet.Homotopy a (v ≫ fiberwisePullbackValueKanComparison p f g b)) := by
  obtain ⟨b₀, s, t, ⟨U⟩, ⟨V⟩⟩ := continuousKanLeftFibration_pair_finite_fiber_detection
    (f ≫ p) (g ≫ p) (a ≫ intervalPullbackLeft _ _) (a ≫ intervalPullbackRight _ _)
  obtain ⟨e, hl, hr, L, _⟩ := intervalPullback_transport_inputs (continuousKanReplacement.map f)
    (continuousKanReplacement.map g) a
    (s ≫ vertexFiberι (f ≫ p) b₀ ≫ continuousKanReplacementUnit.app E)
    (t ≫ vertexFiberι (g ≫ p) b₀ ≫ continuousKanReplacementUnit.app D) U V
  obtain ⟨P, hP⟩ := kanCospanPoint_recognition f g e
    (s ≫ vertexFiberι (f ≫ p) b₀) (t ≫ vertexFiberι (g ≫ p) b₀) hl hr
  obtain ⟨b, v, ⟨T⟩⟩ := fiberwisePullbackKanComparison_original_input_detection p f g
    (s ≫ vertexFiberι (f ≫ p) b₀) (t ≫ vertexFiberι (g ≫ p) b₀) P
  rw [hP] at L
  refine ⟨b, v, ?_⟩
  apply (functorVertex_piZero_eq_iff_homotopy _ _).1
  exact ((functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨L⟩).trans
    ((functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨T⟩)

/-- 概要：構成済み全空間 Kan 比較へ、任意の有限標的射をホモトピーまで持ち上げられる。
方針：元の一値での検出を全空間の単位へ含める。
規約：元の比較射そのもの。使われ方：有限写像空間の全射性。 -/
lemma fiberwisePullbackKanComparison_finite_lifting {K E D H B : SSet.{u}}
    [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
    [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)]
    (a : K ⟶ intervalPullback (continuousKanReplacement.map f) (continuousKanReplacement.map g)) :
    ∃ r : K ⟶ continuousKanReplacement.obj (fiberwiseIntervalPullback p f g),
      Nonempty (SSet.Homotopy a (r ≫ fiberwisePullbackKanComparison p f g)) := by
  obtain ⟨b, v, H⟩ := fiberwisePullbackKanComparison_finite_value_detection p f g a
  exact ⟨v ≫ fiberwisePullbackValueToTotal p f g b ≫
    continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g), H⟩

/-- 概要：有限試験対象の写像空間の連結成分で、元の Kan 引き戻し比較は全射。
方針：各成分の代表を有限持ち上げ定理に渡す。
規約：これだけで弱同値性は結論しない。使われ方：比較の全射側の検証。 -/
lemma fiberwisePullbackKanComparison_mapPiZero_surjective {K E D H B : SSet.{u}}
    [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
    [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)] :
    Function.Surjective (SSet.mapπ₀ ((ihom K).map (fiberwisePullbackKanComparison p f g))) := by
  intro a
  obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective a
  obtain ⟨r, rfl⟩ := (functorVertexEquiv K _).surjective v
  obtain ⟨s, ⟨H⟩⟩ := fiberwisePullbackKanComparison_finite_lifting p f g r
  refine ⟨SSet.π₀.mk (functorVertex s), ?_⟩
  change SSet.π₀.mk (functorVertex (s ≫ fiberwisePullbackKanComparison p f g)) =
    SSet.π₀.mk (functorVertex r)
  exact ((functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨H⟩).symm

end SerrePositivity.InfinityCategories.F2
