module

public import SerrePositivity.KST.Comparison.ActionBarCoordinates
public import SerrePositivity.KST.Comparison.TranslationDescent
public import SerrePositivity.KST.Comparison.ProductHomotopyPullback

/-!
# bar の単体作用の四角形

概要：正則 bar の各行の射影と単体作用を積座標で比較する。
方針：前置ラベルを単体的写像に束ね、作用の移送をパラメータ付き平行移動として表す。
規約：Segal 1974 Proposition 1.6 の仮定の検証。モノイドの Kan 性は要求しない。
使われ方：群状モノイドの bar のファイバー比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
open SerrePositivity.SimplicialModel

/--
概要：bar の nerve の次数を外側に置いた二重単体集合。
方針：モノイドの次数と nerve の次数の二つの添字を交換する。
規約：Segal 1974 Proposition 1.6 の simplicial space に対応する方向。
使われ方：各行の積座標と面の四角形。
-/
abbrev actionBarBase (M : SimplicialObject MonCat.{u}) : SimplicialObject SSet.{u} :=
  (bisimplicialBar M).flip

/--
概要：正則 bar の nerve の次数を外側に置いた二重単体集合。
方針：正則作用の二重単体的 nerve の添字を交換する。
規約：Segal 1974 Proposition 1.6 の全空間。
使われ方：分類空間へ射影する各行の構成。
-/
abbrev actionBarTotal (M : SimplicialObject MonCat.{u}) : SimplicialObject SSet.{u} :=
  (bisimplicialRegularBar M).flip

/--
概要：正則 bar の各行を基底の各行へ射影する。
方針：各射列のラベルを保って一対象圏へ送る。
規約：Segal 1974 Proposition 1.6 の比較の射。
使われ方：単体作用が与える可換四角形。
-/
def actionBarProjection (M : SimplicialObject MonCat.{u}) : actionBarTotal M ⟶ actionBarBase M where
  app _ :=
    { app _ := TypeCat.ofHom (fun E => E ⋙ regularActionProjection _)
      naturality _ _ _ := rfl }
  naturality _ _ _ := rfl

/--
概要：各行の積座標の第一射影は bar の射影である。
方針：積座標の定義の第一成分を評価する。
規約：Segal 1974 Proposition 1.6 の座標。
使われ方：射影の別の Kan 分解。
-/
theorem regularBarRowIso_fst (M : SimplicialObject MonCat.{u}) (r : ℕ) :
    (regularBarRowIso M r).hom ≫ fst ((actionBarBase M).obj (op ⦋r⦌)) (monoidSpace M) =
      (actionBarProjection M).app (op ⦋r⦌) := rfl

/--
概要：bar の各行の始点から指定頂点への前置ラベルを単体的写像へ束ねる。
方針：各モノイド次数で前置ラベルを取り出す。
規約：Segal 1974 Proposition 1.6 のファイバー移送の元の族。
使われ方：全パラメータでの左平行移動。
-/
def actionBarPrefix (M : SimplicialObject MonCat.{u}) {r : ℕ} (i : Fin (r + 1)) :
    (actionBarBase M).obj (op ⦋r⦌) ⟶ monoidSpace M where
  app n := TypeCat.ofHom (fun F => monoidPrefixLabel (M.obj n) F i)
  naturality _ _ _ := rfl

/--
概要：単体作用と積座標の交換は、前置ラベルの作用と基底の単体作用で表される。
方針：各射列に対して始点座標の移送式を適用する。
規約：Segal 1974 Proposition 1.6 の全ての面と退化の四角形。
使われ方：群状性による各行の比較写像の局所化可逆性。
-/
theorem actionBarCoordinate_naturality (M : SimplicialObject MonCat.{u}) {n m : ℕ}
    (θ : (op ⦋n⦌ : SimplexCategoryᵒᵖ) ⟶ op ⦋m⦌) :
    (actionBarTotal M).map θ ≫ (regularBarRowIso M m).hom =
      (regularBarRowIso M n).hom ≫
        monoidActionFamily M (actionBarPrefix M (θ.unop.toOrderHom 0)) ≫
          (actionBarBase M).map θ ▷ monoidSpace M := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro E
  exact regularActionCoordinate_whisker (M.obj d) E (SimplexCategory.toCat.map θ.unop).toFunctor
/--
概要：正則 bar の射影と単体作用が与える可換四角形。
方針：射影の二重単体的自然性を使う。
規約：Segal 1974 Proposition 1.6 の仮定の四角形。
使われ方：行ごとのホモトピー引き戻し性。
-/
theorem actionBarSquare (M : SimplicialObject MonCat.{u}) {n m : ℕ}
    (θ : (op ⦋n⦌ : SimplexCategoryᵒᵖ) ⟶ op ⦋m⦌) :
    CommSq ((actionBarProjection M).app (op ⦋n⦌)) ((actionBarTotal M).map θ)
      ((actionBarBase M).map θ) ((actionBarProjection M).app (op ⦋m⦌)) :=
  ⟨((actionBarProjection M).naturality θ).symm⟩

/--
概要：群状モノイドの正則 bar の全ての単体作用の四角形はホモトピー引き戻しである。
方針：各行を基底とモノイドの積にし、前置ラベルの作用とファイバーだけの Kan 置換で比較射を計算する。
規約：Segal 1974 Proposition 1.6 の仮定を証明する。元のモノイドの Kan 性は不要。
使われ方：対角での bar のホモトピーファイバー比較。
-/
theorem actionBarSquare_isHomotopyPullback (M : SimplicialObject MonCat.{u})
    (hG : SimplicialMonoid.IsGrouplike M) {n m : ℕ}
    (θ : (op ⦋n⦌ : SimplexCategoryᵒᵖ) ⟶ op ⦋m⦌) :
    IsHomotopyPullback (actionBarSquare M θ) := by
  let Bn := (actionBarBase M).obj (op ⦋n⦌)
  let Bm := (actionBarBase M).obj (op ⦋m⦌)
  let En := (actionBarTotal M).obj (op ⦋n⦌)
  let Em := (actionBarTotal M).obj (op ⦋m⦌)
  let rn : En ≅ Bn ⊗ monoidSpace M := regularBarRowIso M n
  let rm : Em ≅ Bm ⊗ monoidSpace M := regularBarRowIso M m
  let f : Bn ⟶ Bm := (actionBarBase M).map θ
  let t : En ⟶ Em := (actionBarTotal M).map θ
  let R := AnodyneKanReplacement.functor.obj (monoidSpace M)
  let e : monoidSpace M ⟶ R := AnodyneKanReplacement.unit.app (monoidSpace M)
  let i : Em ⟶ Bm ⊗ R := rm.hom ≫ Bm ◁ e
  let p : Bm ⊗ R ⟶ Bm := fst Bm R
  have hi : SSet.anodyneExtensions i :=
    SSet.anodyneExtensions.comp_mem _ _ (SSet.anodyneExtensions.of_isIso rm.hom)
      ((AnodyneKanReplacement.unit_anodyne (monoidSpace M)).whiskerLeft Bm)
  let : SSet.KanComplex R := kanReplacement_kan (monoidSpace M)
  have hp : SSet.modelCategoryQuillen.J.rlp p := productProjection_rlp Bm R
  have hi_fac : i ≫ p = (actionBarProjection M).app (op ⦋m⦌) := by
    dsimp only [i, p]
    rw [Category.assoc, whiskerLeft_fst]
    exact regularBarRowIso_fst M m
  apply (isHomotopyPullback_iff_alternative (actionBarSquare M θ) i hi p hp hi_fac).mpr
  let A : Bn ⊗ monoidSpace M ⟶ Bn ⊗ monoidSpace M :=
    monoidActionFamily M (actionBarPrefix M (θ.unop.toOrderHom 0))
  let v : En ⟶ Bn ⊗ R := rn.hom ≫ A ≫ Bn ◁ e
  let c := (productPullbackSquare f R).isoPullback
  have hA : A ≫ fst Bn (monoidSpace M) = fst Bn (monoidSpace M) := rfl
  have hrn : rn.hom ≫ fst Bn (monoidSpace M) =
      (actionBarProjection M).app (op ⦋n⦌) := regularBarRowIso_fst M n
  have hvf : v ≫ fst Bn R = (actionBarProjection M).app (op ⦋n⦌) := by
    simp only [v, Category.assoc, whiskerLeft_fst, hA, hrn]
  have hcoord : t ≫ rm.hom = rn.hom ≫ A ≫ f ▷ monoidSpace M := actionBarCoordinate_naturality M θ
  have hvs : v ≫ f ▷ R = t ≫ i := by
    calc
      v ≫ f ▷ R = rn.hom ≫ A ≫ (Bn ◁ e ≫ f ▷ R) := by simp only [v, Category.assoc]
      _ = rn.hom ≫ A ≫ (f ▷ monoidSpace M ≫ Bm ◁ e) := by rw [whisker_exchange]
      _ = (rn.hom ≫ A ≫ f ▷ monoidSpace M) ≫ Bm ◁ e := by simp only [Category.assoc]
      _ = (t ≫ rm.hom) ≫ Bm ◁ e := congrArg (fun k => k ≫ Bm ◁ e) hcoord.symm
      _ = t ≫ i := by dsimp only [i]; rw [Category.assoc]
  have hfac : alternativePullbackComparison (actionBarSquare M θ) i p hi_fac = v ≫ c.hom := by
    apply pullback.hom_ext
    · rw [alternativePullbackComparison_fst, Category.assoc,
        (productPullbackSquare f R).isoPullback_hom_fst]
      exact hvf.symm
    · rw [alternativePullbackComparison_snd, Category.assoc,
        (productPullbackSquare f R).isoPullback_hom_snd]
      exact hvs.symm
  have : IsIso (AnodyneHomotopy.anodyneQ.map A) :=
    monoidActionFamily_localized_isIso M hG _
  have : IsIso (AnodyneHomotopy.anodyneQ.map (Bn ◁ e)) :=
    Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
      ((AnodyneKanReplacement.unit_anodyne (monoidSpace M)).whiskerLeft Bn)
  rw [hfac]
  dsimp only [v]
  simp only [AnodyneHomotopy.anodyneQ.map_comp]
  infer_instance


end SerrePositivity.KST.Comparison
