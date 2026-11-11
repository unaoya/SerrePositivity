module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberComparisonExt
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberComparisonComponents
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberConnectingIndependence

/-! # Cofiber と suspension の比較の合成

概要：指定 suspension への標準比較は suspension 間の標準比較の合成と両立する。
方針：始点成分を等号による輸送として計算し、比較の始点成分による判定を使う。
規約：四角形そのものを変えず、指定した始点の表示だけを輸送する。
使われ方：S4 の接続射の suspension の変更との整合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：suspension 四角形の指定始点の表示を等号に沿って変更する。
方針：始点の等式を合成し、四角形と普遍性をそのまま使う。
規約：四角形は厳密に同じ。使われ方：同じ始点の suspension の比較の合成。 -/
def SuspensionSquare.changeSource {X : SSet.{u}} {x y : X _⦋0⦌}
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) (h : x = y) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare y :=
  { s with source_eq := s.source_eq.trans h }

/-- 概要：四角形の関手圏の h から指定角での評価関手を得る。
方針：単体的な頂点評価を hoFunctor で送る。
規約：四角形の横・縦の順序を保つ。使われ方：比較の成分と合成の計算。 -/
def squareDiagramHoEvaluation (X : SSet.{u}) (i j : Fin 2) :
    hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) ⥤ hoFunctor.obj X :=
  (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) i j))).toFunctor

/-- 概要：選んだ始点固定の比較を四角形の関手圏の h の射として表す。
方針：比較ホモトピーの関手辺の類を取る。
規約：元の四角形は押し出し。使われ方：比較の合成と頂点成分の評価。 -/
def cofiberSuspensionComparisonHom {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0)) :
    (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.square) :=
  SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSuspensionComparison F hF s))

/-- 概要：標準比較を始点で評価すると始点の等号による輸送になる。
方針：固定頂点での評価を恒等射と Arrow として照合し、端点の輸送を計算する。
規約：零射構造は不要。使われ方：比較の合成の始点での判定。 -/
lemma cofiberSuspensionComparisonHom_source {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0)) :
    (squareDiagramHoEvaluation X 0 0).map (cofiberSuspensionComparisonHom F hF s) =
      eqToHom (show _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex F 0 0 = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex s.square 0 0 from
        congrArg SSet.HomotopyCategory.mk s.source_eq.symm) := by
  let H := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSuspensionComparison F hF s
  have hi : SSet.yonedaEquiv
      (stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge : (Δ[0] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0 := by
    apply Prod.ext <;> decide
  have ha := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyEvaluation_arrow H
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0)
  have hb := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyNatTrans_fixedVertex_arrow H.h
    (stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSuspensionComparison_source F hF s)
  rw [hi] at hb
  have hab := ha.trans hb
  obtain ⟨hX, hY, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp hab
  simpa only [H, squareDiagramHoEvaluation, cofiberSuspensionComparisonHom,
    eqToHom_refl, Category.id_comp] using hf

/-- 概要：標準比較の最後の成分は指定 suspension への接続射である。
方針：両端を指定したホモトピーの自然変換の成分と評価した類を照合する。
規約：任意の零射構造。使われ方：比較の合成から接続射の整合を導く。 -/
lemma cofiberSuspensionComparisonHom_target {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0)) :
    (squareDiagramHoEvaluation X 1 1).map (cofiberSuspensionComparisonHom t.square ht s) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension t ht s := by
  apply Arrow.mk_injective
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyEvaluationOfEndpoints_arrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSuspensionComparison t.square ht s)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 1)

/-- 概要：指定 suspension への比較は中間の suspension を経由した比較の合成に等しい。
方針：両辺の始点成分を輸送の合成として計算し、始点評価の単射性を適用する。
規約：二つの suspension は元の四角形と同じ指定始点を持つ。
使われ方：接続射の suspension の変更との整合。 -/
lemma cofiberSuspensionComparisonHom_comp {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F)
    (s r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0)) :
    cofiberSuspensionComparisonHom F hF s ≫
      cofiberSuspensionComparisonHom s.square s.isPushout (r.changeSource s.source_eq.symm) =
        cofiberSuspensionComparisonHom F hF r := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparison_hom_ext F hF r
  change (squareDiagramHoEvaluation X 0 0).map _ = (squareDiagramHoEvaluation X 0 0).map _
  rw [Functor.map_comp, cofiberSuspensionComparisonHom_source,
    cofiberSuspensionComparisonHom_source, cofiberSuspensionComparisonHom_source, eqToHom_trans]

/-- 概要：接続射は中間の suspension を経由する標準比較の合成と両立する。
方針：四角形の標準比較の合成則を最後の頂点で評価する。
規約：指定始点の表示だけを変更する。使われ方：接続射の選択の比較。 -/
lemma cofiberConnectingToSuspension_comp {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t)
    (s r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension t ht s ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension s.toZeroTriangle s.isPushout
        (r.changeSource s.source_eq.symm) = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension t ht r := by
  have h := congrArg (fun f ↦ (squareDiagramHoEvaluation X 1 1).map f)
    (cofiberSuspensionComparisonHom_comp t.square ht s r)
  simpa only [Functor.map_comp, cofiberSuspensionComparisonHom_target] using h

/-- 概要：cofiber 四角形と suspension 四角形の二つの比較が始点で可換なら標準比較と可換。
方針：二つの合成を始点で照合し、指定 suspension への射の一意性を適用する。
規約：二つの cofiber 四角形の始点は異なってよい。
使われ方：接続射の自然性を始点での条件へ帰着する。 -/
lemma cofiberSuspensionComparisonHom_naturality {X : SSet.{u}} [Quasicategory X]
    (F G : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare G)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex G 0 0))
    (a : (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
    (b : (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.square) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex r.square))
    (h : (squareDiagramHoEvaluation X 0 0).map a ≫
      eqToHom (congrArg SSet.HomotopyCategory.mk r.source_eq.symm) =
        eqToHom (congrArg SSet.HomotopyCategory.mk s.source_eq.symm) ≫
          (squareDiagramHoEvaluation X 0 0).map b) :
    a ≫ cofiberSuspensionComparisonHom G hG r = cofiberSuspensionComparisonHom F hF s ≫ b := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparison_hom_ext F hF r
  change (squareDiagramHoEvaluation X 0 0).map _ = (squareDiagramHoEvaluation X 0 0).map _
  rw [Functor.map_comp, Functor.map_comp, cofiberSuspensionComparisonHom_source,
    cofiberSuspensionComparisonHom_source]
  exact h

/-- 概要：始点で可換な四角形の比較と suspension の比較に対して接続射が可換になる。
方針：標準比較の自然性を最後の頂点で評価する。
規約：suspension 間の射と始点での可換式を入力する。
使われ方：Σ の関手性との照合前の接続射の自然性。 -/
lemma cofiberConnectingToSuspension_naturality {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] (t d : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X)
    (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) (hd : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence d)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0))
    (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.square 0 0))
    (a : (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.square) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d.square))
    (b : (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.square) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex r.square))
    (h : (squareDiagramHoEvaluation X 0 0).map a ≫
      eqToHom (congrArg SSet.HomotopyCategory.mk r.source_eq.symm) =
        eqToHom (congrArg SSet.HomotopyCategory.mk s.source_eq.symm) ≫
          (squareDiagramHoEvaluation X 0 0).map b) :
    (squareDiagramHoEvaluation X 1 1).map a ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension d hd r =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension t ht s ≫ (squareDiagramHoEvaluation X 1 1).map b := by
  have he := congrArg (fun f ↦ (squareDiagramHoEvaluation X 1 1).map f)
    (cofiberSuspensionComparisonHom_naturality t.square d.square ht hd s r a b h)
  simpa only [Functor.map_comp, cofiberSuspensionComparisonHom_target] using he

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
