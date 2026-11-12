module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneKanReplacement
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# bar 比較に用いるホモトピー引き戻しの模型

概要：右の射を horn に対する fibration へ関手的に置換して引き戻す。
方針：小対象論法の anodyne–fibration 分解から比較先と標準比較射を明示する。
規約：Segal 1974 Proposition 1.6・Lemma 1.7・1.8 の対角模型への移植の界面。
使われ方：厳密ファイバーとホモトピーファイバーを区別する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel

/--
概要：右射を Kan fibration へ置換した引き戻し対象。
方針：右射の horn 小対象分解の後半を左射に沿って引き戻す。
規約：Segal 1974 Proposition 1.6 の固定したホモトピー引き戻し模型。
使われ方：bar の四角形の標準比較射の終域。
-/
def homotopyPullbackObject {X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) : SSet.{u} :=
  pullback f (AnodyneKanReplacement.factorization.p.app (Arrow.mk g))

/--
概要：ホモトピー引き戻し模型の左射影は Kan fibration である。
方針：右射の置換の右持ち上げ性と引き戻し閉性を使う。
規約：Segal 1974 Proposition 1.6 の比較先。弱同値のモデル構造は仮定しない。
使われ方：ホモトピーファイバーの Kan 性と長完全列への接続。
-/
instance homotopyPullbackProjection_fibration {X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Fibration (pullback.fst f (AnodyneKanReplacement.factorization.p.app (Arrow.mk g))) := by
  let p := AnodyneKanReplacement.factorization.p.app (Arrow.mk g)
  let : Fibration p := (SSet.modelCategoryQuillen.fibration_iff p).mpr
    (AnodyneKanReplacement.factorization.hp _)
  let : (fibrations SSet.{u}).IsStableUnderBaseChange := by
    rw [fibrations_eq]
    infer_instance
  infer_instance

/--
概要：左の対象が Kan ならホモトピー引き戻し模型も Kan である。
方針：左射影の fibration と終射の fibration を合成する。
規約：Segal 1974 Proposition 1.6 のホモトピー群への入力。
使われ方：基点の引き戻しによるホモトピーファイバー。
-/
instance homotopyPullbackObject_kan {X Y Z : SSet.{u}} [SSet.KanComplex X]
    (f : X ⟶ Z) (g : Y ⟶ Z) : SSet.KanComplex (homotopyPullbackObject f g) := by
  let : (fibrations SSet.{u}).IsStableUnderComposition := by
    rw [fibrations_eq]
    infer_instance
  exact isFibrant_of_fibration
    (pullback.fst f (AnodyneKanReplacement.factorization.p.app (Arrow.mk g)))

/--
概要：可換四角形の頂点から置換した引き戻しへの標準比較射。
方針：右の成分に anodyne 分解の前半を合成し、引き戻しの普遍性を使う。
規約：Segal 1974 Proposition 1.6。元の四角形の普遍性は仮定しない。
使われ方：ホモトピー引き戻し性を判定する実際の射。
-/
def homotopyPullbackComparison {P X Y Z : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : CommSq a b f g) :
    P ⟶ homotopyPullbackObject f g :=
  pullback.lift a (b ≫ AnodyneKanReplacement.factorization.i.app (Arrow.mk g)) (by
    rw [Category.assoc, AnodyneKanReplacement.factorization.fac_app]
    exact sq.w)

/--
概要：標準比較射の左射影は元の四角形の左成分である。
方針：引き戻しへの持ち上げの計算則を使う。
規約：Segal 1974 Proposition 1.6 の比較射の規約。
使われ方：基底上の比較の可換性。
-/
@[reassoc] theorem homotopyPullbackComparison_fst {P X Y Z : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : CommSq a b f g) :
    homotopyPullbackComparison sq ≫ pullback.fst f
      (AnodyneKanReplacement.factorization.p.app (Arrow.mk g)) = a := pullback.lift_fst ..

/--
概要：標準比較射の右射影は元の右成分の anodyne 置換である。
方針：引き戻しへの持ち上げの計算則を使う。
規約：Segal 1974 Proposition 1.6 の比較射の規約。
使われ方：関手的な置換との整合。
-/
@[reassoc] theorem homotopyPullbackComparison_snd {P X Y Z : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : CommSq a b f g) :
    homotopyPullbackComparison sq ≫ pullback.snd f
      (AnodyneKanReplacement.factorization.p.app (Arrow.mk g)) =
        b ≫ AnodyneKanReplacement.factorization.i.app (Arrow.mk g) := pullback.lift_snd ..

/--
概要：可換な基底の比較はホモトピー引き戻し模型の間の標準射を誘導する。
方針：右射の分解の関手性を用い、二つの射影を比較先へ送る。
規約：Segal 1974 Proposition 1.6・Lemma 1.7 の基底付き比較。
使われ方：骨格の貼り合わせの図式の構成。
-/
def homotopyPullbackMap {X Y Z X' Y' Z' : SSet.{u}}
    {f : X ⟶ Z} {g : Y ⟶ Z} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    (a : X ⟶ X') (b : Y ⟶ Y') (c : Z ⟶ Z')
    (hf : f ≫ c = a ≫ f') (hg : g ≫ c = b ≫ g') :
    homotopyPullbackObject f g ⟶ homotopyPullbackObject f' g' := by
  let φ : Arrow.mk g ⟶ Arrow.mk g' := Arrow.homMk b c hg.symm
  let p := AnodyneKanReplacement.factorization.p.app (Arrow.mk g)
  let p' := AnodyneKanReplacement.factorization.p.app (Arrow.mk g')
  let q := AnodyneKanReplacement.factorization.Z.map φ
  refine pullback.lift (pullback.fst f p ≫ a) (pullback.snd f p ≫ q) ?_
  calc
    (pullback.fst f p ≫ a) ≫ f' = pullback.fst f p ≫ (f ≫ c) := by
      rw [Category.assoc, hf]
    _ = (pullback.snd f p ≫ p) ≫ c := by
      rw [← Category.assoc, pullback.condition]
    _ = (pullback.snd f p ≫ q) ≫ p' := by
      have h := AnodyneKanReplacement.factorization.p.naturality φ
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun k => pullback.snd f p ≫ k) h.symm).trans (Category.assoc _ _ _).symm)

/--
概要：固定した置換模型における四角形のホモトピー引き戻し性。
方針：標準比較射が anodyne 局所化で同型となることを要求する。
規約：Segal 1974 Proposition 1.6。性質の定義であり、bar の比較定理の仮定ではない。
使われ方：貼り合わせと対角比較で証明すべき結論の型。
-/
@[kerodon 010L]
def IsHomotopyPullback {P X Y Z : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : CommSq a b f g) : Prop :=
  IsIso (AnodyneHomotopy.anodyneQ.map (homotopyPullbackComparison sq))

end SerrePositivity.KST.Comparison
