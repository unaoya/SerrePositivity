module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberComparisonComposition

/-! # Suspension 間の標準比較同型と接続射

概要：同じ始点の suspension 間の標準比較は同型であり、接続射を互いに移す。
方針：始点成分による一意性で恒等・合成則を証明し、最後の頂点で評価する。
規約：特定の零頂点の選択には依存しない。
使われ方：S4 の接続射の suspension の変更に関する照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：suspension から自身への標準比較は恒等射である。
方針：始点成分を恒等射と照合し、比較の一意性で戻す。
規約：始点の表示だけを元の四角形の始点に戻す。使われ方：標準比較の可逆性。 -/
lemma cofiberSuspensionComparisonHom_self {X : SSet.{u}} [Quasicategory X]
    {x : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom s.square s.isPushout (s.changeSource s.source_eq.symm) =
      𝟙 (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.square)) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparison_hom_ext s.square s.isPushout (s.changeSource s.source_eq.symm)
  change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map _ = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom_source]
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare.changeSource]
  change (𝟙 ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).obj
    (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.square)))) = _
  exact ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map_id
    (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.square))).symm

/-- 概要：同じ始点の二つの suspension 四角形は関手圏の h で標準的に同型。
方針：両方向の標準比較を取り、合成則と自身への比較の恒等性で逆性を証明する。
規約：始点での成分は等号による輸送。使われ方：suspension の頂点の比較同型。 -/
def SuspensionSquare.diagramComparisonIso {X : SSet.{u}} [Quasicategory X]
    {x : X _⦋0⦌} (s r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.square) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ≅
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex r.square) where
  hom := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom s.square s.isPushout (r.changeSource s.source_eq.symm)
  inv := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom r.square r.isPushout (s.changeSource r.source_eq.symm)
  hom_inv_id := by
    have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom_comp s.square s.isPushout
      (r.changeSource s.source_eq.symm) (s.changeSource s.source_eq.symm)
    exact h.trans (cofiberSuspensionComparisonHom_self s)
  inv_hom_id := by
    have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom_comp r.square r.isPushout
      (s.changeSource r.source_eq.symm) (r.changeSource r.source_eq.symm)
    exact h.trans (cofiberSuspensionComparisonHom_self r)

/-- 概要：同じ suspension の四角形の標準比較同型は恒等同型である。
方針：順方向の射を恒等射と照合する。
規約：指定始点を保つ。使われ方：比較同型の単位則。 -/
lemma SuspensionSquare.diagramComparisonIso_self {X : SSet.{u}} [Quasicategory X]
    {x : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    s.diagramComparisonIso s = Iso.refl _ := by
  apply Iso.ext
  exact cofiberSuspensionComparisonHom_self s

/-- 概要：suspension 四角形の標準比較同型は三つの選択の間で合成則を満たす。
方針：順方向の射に標準比較の合成則を適用する。
規約：三つとも同じ指定始点。使われ方：選択変更の整合性。 -/
lemma SuspensionSquare.diagramComparisonIso_trans {X : SSet.{u}} [Quasicategory X]
    {x : X _⦋0⦌} (s r q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    s.diagramComparisonIso r ≪≫ r.diagramComparisonIso q = s.diagramComparisonIso q := by
  apply Iso.ext
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom_comp s.square s.isPushout
    (r.changeSource s.source_eq.symm) (q.changeSource s.source_eq.symm)

/-- 概要：同じ始点の suspension 頂点の間の標準比較同型。
方針：四角形間の比較同型を最後の頂点で評価する。
規約：X の安定性全体は不要。使われ方：接続射の値域の選択を変更する。 -/
def SuspensionSquare.comparisonIso {X : SSet.{u}} [Quasicategory X]
    {x : X _⦋0⦌} (s r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    (SSet.HomotopyCategory.mk s.vertex : hoFunctor.obj X) ≅
      SSet.HomotopyCategory.mk r.vertex :=
  (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).mapIso (s.diagramComparisonIso r)

/-- 概要：suspension 頂点の自身への標準比較同型は恒等同型である。
方針：四角形の比較同型の単位則を最後の頂点で評価する。
規約：安定性は不要。使われ方：対象の選択変更の単位。 -/
lemma SuspensionSquare.comparisonIso_self {X : SSet.{u}} [Quasicategory X]
    {x : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) : s.comparisonIso s = Iso.refl _ := by
  simp only [comparisonIso, diagramComparisonIso_self, Functor.mapIso_refl]
  rfl

/-- 概要：suspension 頂点の標準比較同型は三つの選択の間で合成則を満たす。
方針：四角形の比較同型の合成則を最後の頂点で評価する。
規約：三つとも同じ指定始点。使われ方：接続射の値域の選択変更の整合性。 -/
lemma SuspensionSquare.comparisonIso_trans {X : SSet.{u}} [Quasicategory X]
    {x : X _⦋0⦌} (s r q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    s.comparisonIso r ≪≫ r.comparisonIso q = s.comparisonIso q := by
  simpa only [comparisonIso, Functor.mapIso_trans] using
    congrArg (fun e ↦ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).mapIso e) (s.diagramComparisonIso_trans r q)

/-- 概要：suspension の標準比較同型の順方向の射は、その cofiber 列の接続射である。
方針：比較同型の定義と最後の頂点での評価の式。
規約：任意の零射構造。使われ方：接続射の値域の輸送。 -/
lemma SuspensionSquare.comparisonIso_hom {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] {x : X _⦋0⦌} (s r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    (s.comparisonIso r).hom = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension s.toZeroTriangle s.isPushout
      (r.changeSource s.source_eq.symm) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom_target s.toZeroTriangle s.isPushout
    (r.changeSource s.source_eq.symm)

/-- 概要：接続射は suspension 頂点の標準比較同型で互いに移る。
方針：標準比較の合成則を接続射として読み、比較同型の順方向の射を代入する。
規約：元の cofiber 列と同じ始点の二つの suspension。使われ方：接続射の選択の比較。 -/
lemma cofiberConnectingToSuspension_comparisonIso {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t)
    (s r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension t ht s ≫ (s.comparisonIso r).hom =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension t ht r := by
  rw [SuspensionSquare.comparisonIso_hom]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension_comp t ht s r

/-- 概要：Σ を値域とする接続射は任意の suspension を経由して計算できる。
方針：標準比較で選択済みの suspension へ移し、その頂点の Σ との同型を合成する。
規約：元の suspensionFunctorObjIso との一般の整合は別の主張。
使われ方：接続射の具体的な計算と値域の選択変更。 -/
lemma cofiberConnecting_eq_via_suspensionComparison {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension t ht s ≫
      (s.comparisonIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenSuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0))).hom ≫
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenSuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0)).suspensionFunctorObjIso.inv =
          _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht := by
  rw [← Category.assoc, cofiberConnectingToSuspension_comparisonIso]
  rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
