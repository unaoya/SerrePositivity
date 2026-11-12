module

public import SerrePositivity.KST.Comparison.BarEdge
public import SerrePositivity.KST.Comparison.LoopFamily
public import SerrePositivity.KST.Spectra.SuspensionLoop
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneKanReplacement

/-!
# bar の Kan 置換からの群完備化空間

概要：Kan 置換した BM の基点付きループ空間を群完備化の比較先として構成する。
方針：horn の小対象論法による置換と K-L9 の実際のループ対象を借りる。
規約：Segal 1974 Proposition 1.5、KST Lemma 2.13。群状性による比較同値は別途証明する。
使われ方：標準ループ族の随伴先と群完備化比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.SimplicialModel

/--
概要：bar の Kan 置換に元の bar の基点の像を選ぶ。
方針：anodyne 置換の単位の零次成分を基点へ適用する。
規約：Segal 1974 Proposition 1.5 の分類空間の点付き Kan 模型。
使われ方：K-L9 のループ空間への入力。
-/
def monoidBarKanPointed (M : SimplicialObject MonCat.{u}) : PointedSimplicialSet.{u} :=
  PointedSimplicialSet.ofVertex (AnodyneKanReplacement.functor.obj (monoidBar M))
    ((AnodyneKanReplacement.unit.app (monoidBar M)).app (op ⦋0⦌) (monoidBarBasepoint M))

/--
概要：bar の置換は全 horn を充填する Kan 複体である。
方針：小対象論法の終射の右持ち上げ性を Kan fibration の条件へ移す。
規約：Segal 1974 Proposition 1.5 のループ空間の模型。値宇宙のモデル構造は仮定しない。
使われ方：ループ対象の Kan 性。
-/
instance monoidBarKanPointed_kan (M : SimplicialObject MonCat.{u}) :
    KanComplex (monoidBarKanPointed M).right := by
  change Fibration (terminal.from (AnodyneKanReplacement.functor.obj (monoidBar M)))
  exact (SSet.modelCategoryQuillen.fibration_iff _).mpr
    (AnodyneKanReplacement.terminal_rlp (monoidBar M))

/--
概要：群完備化の比較先を Kan 置換した BM のループ空間として定義する。
方針：K-L9 の単体的円からの点付き内部 Hom を使う。
規約：Segal 1974 Proposition 1.5。群状モノイドからの同値性はこの定義に含めない。
使われ方：KST Lemma 2.13 の delooping 比較。
-/
def monoidGroupCompletionSpace (M : SimplicialObject MonCat.{u}) : PointedSimplicialSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (monoidBarKanPointed M)

/--
概要：群完備化の比較先は Kan 複体である。
方針：K-L9 のループ空間の相対 horn 充填を適用する。
規約：Segal 1974 Proposition 1.5。元のモノイドに Kan 性を要求しない。
使われ方：比較先のホモトピー群。
-/
instance monoidGroupCompletionSpace_kan (M : SimplicialObject MonCat.{u}) :
    KanComplex (monoidGroupCompletionSpace M).right := by
  dsimp only [monoidGroupCompletionSpace]
  infer_instance

/--
概要：Kan 置換した bar での各元の基点ループの族。
方針：標準辺写像に Kan 置換の単位を後合成する。
規約：Segal 1974 Proposition 1.5 の標準写像の随伴側。
使われ方：円の商の普遍性によるループ空間への射の構成。
-/
def groupCompletionLoopFamily (M : SimplicialObject MonCat.{u}) :
    SSet.Homotopy (SSet.const (X := monoidSpace M)
      (PointedSimplicialSet.basepoint (monoidBarKanPointed M)))
      (SSet.const (PointedSimplicialSet.basepoint (monoidBarKanPointed M))) where
  h := monoidBarEdgeMap M ≫ AnodyneKanReplacement.unit.app (monoidBar M)
  h₀ := by
    rw [← Category.assoc, monoidBarEdgeMap_zero, SSet.const_comp]
    simp only [monoidBarKanPointed, PointedSimplicialSet.basepoint_ofVertex]
    rfl
  h₁ := by
    rw [← Category.assoc, monoidBarEdgeMap_one, SSet.const_comp]
    simp only [monoidBarKanPointed, PointedSimplicialSet.basepoint_ofVertex]
    rfl
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property
/--
概要：単体的モノイドから Kan な群完備化空間への標準写像。
方針：Kan 置換した bar のループ族を円の商へ降ろし、K-L9 のループ空間へ転置する。
規約：Segal 1974 Proposition 1.5、KST Lemma 2.13。群状性による同値性は別途必要。
使われ方：群完備化比較の実際の射。
-/
def monoidGroupCompletionMap (M : SimplicialObject MonCat.{u}) :
    monoidSpace M ⟶ (monoidGroupCompletionSpace M).right :=
  loopFamilyMap (monoidBarKanPointed M) (groupCompletionLoopFamily M)

/--
概要：群完備化の標準写像を区間上で評価すると元の bar の辺写像の Kan 置換になる。
方針：ループ族からの写像の評価の計算則を具体的な族へ適用する。
規約：Segal 1974 Proposition 1.5、KST Lemma 2.13 の標準比較写像。
使われ方：ホモトピーファイバー比較が扱う射との同定。
-/
theorem monoidGroupCompletionMap_evaluation (M : SimplicialObject MonCat.{u}) :
    PointedObject.cofiberQuotient (SSet.boundary.{u} 1).ι ▷ monoidSpace M ≫
      MonoidalClosed.uncurry (monoidGroupCompletionMap M ≫
        PointedObject.basedHomι PointedSimplicialSet.circle (monoidBarKanPointed M)) =
      (β_ (Δ[1] : SSet.{u}) (monoidSpace M)).hom ≫ monoidBarEdgeMap M ≫
        AnodyneKanReplacement.unit.app (monoidBar M) :=
  loopFamilyMap_evaluation (monoidBarKanPointed M) (groupCompletionLoopFamily M)


end SerrePositivity.KST.Comparison
