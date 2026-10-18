module

public import SerrePositivity.KST.ProExcision.AdjacentCut
public import SerrePositivity.KST.ProExcision.FiltrationConnecting

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 項濾過の任意区間と連結写像

概要：実際の項濾過の区間を、次数ごと分裂する商短完全列で表す。
方針：二重切り詰めの同型で短完全性を移し、濾過の δ の一般比較を適用する。
規約：有限添字への制限も同じ関手で扱い、添字の算術的等式による型変換を避ける。
使われ方：KST Lemma 4.10 の初頁微分と有限 Koszul 濾過。
-/

universe u v

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open SerrePositivity.StupidTruncation

variable {R : Type u} [CommRing R]

/-- 概要：二つの下端の間の項濾過の商を短複体にする。
方針：標準の商射を残し、第一射には実際の包含遷移を使う。
規約：b ≤ a。使われ方：KST Lemma 4.10 の有限添字での区間模型。 -/
def intervalCutShortComplex (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) (hab : b ≤ a) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) := by
  let S := StupidTruncation.shortComplex (above P b) a
  refine ShortComplex.mk (truncationInclusion P a b hab) S.g ?_
  rw [← aboveAboveIso_inv_comp_inclusion P a b hab, Category.assoc]
  change (aboveAboveIso P a b hab).inv ≫ (S.f ≫ S.g) = 0
  rw [S.zero, comp_zero]

/-- 概要：区間短複体と標準切り詰め短複体の同型。
方針：第一項を二重切り詰めの逆同型で比較する。
規約：第二項と商は同一。使われ方：KST Lemma 4.10 の分裂と完全性の移送。 -/
def intervalCutIso (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) (hab : b ≤ a) :
    intervalCutShortComplex P a b hab ≅ StupidTruncation.shortComplex (above P b) a := by
  refine ShortComplex.isoMk (aboveAboveIso P a b hab).symm
    (Iso.refl _) (Iso.refl _) ?_ ?_
  · change (aboveAboveIso P a b hab).inv ≫ inclusion (above P b) a =
      truncationInclusion P a b hab ≫ 𝟙 _
    rw [Category.comp_id]
    exact aboveAboveIso_inv_comp_inclusion P a b hab
  · change 𝟙 _ ≫ (StupidTruncation.shortComplex (above P b) a).g =
      (StupidTruncation.shortComplex (above P b) a).g ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]

/-- 概要：区間短複体の次数ごとの分裂。
方針：標準切り詰めの分裂を区間同型に沿って移す。
規約：複体の分裂ではない。使われ方：KST Lemma 4.10 の δ の計算。 -/
def intervalCutSplitting (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) (hab : b ≤ a) (n : ℤ) :
    ((intervalCutShortComplex P a b hab).map (eval _ _ n)).Splitting :=
  (StupidTruncation.splitting (above P b) a n).ofIso
    ((eval (ModuleCat.{u} R) (.up ℤ) n).mapShortComplex.mapIso (intervalCutIso P a b hab).symm)

/-- 概要：任意の項濾過区間の短完全性。
方針：標準切り詰め短完全列との同型を使う。
規約：隣接性は不要。使われ方：KST Lemma 4.10 の商比較。 -/
theorem intervalCutShortComplex_shortExact
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) (hab : b ≤ a) :
    (intervalCutShortComplex P a b hab).ShortExact :=
  ShortComplex.shortExact_of_iso (intervalCutIso P a b hab).symm
    (stupidTruncation_module_shortExact (above P b) a)

/-- 概要：全テンソル後の項濾過区間。
方針：区間短複体を同じ右テンソル関手で写す。
規約：任意の係数複体。使われ方：KST Lemma 4.10 の実際の濾過。 -/
def intervalTensorCutShortComplex (P K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) (hab : b ≤ a) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  cochainTensorShortComplexRight (intervalCutShortComplex P a b hab) K

/-- 概要：全テンソル後の区間短複体の次数ごとの分裂。
方針：元の区間分裂をテンソルで写す。
規約：平坦性は不要。使われ方：KST Lemma 4.10 の区間境界。 -/
def intervalTensorCutSplitting (P K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) (hab : b ≤ a) (n : ℤ) :
    ((intervalTensorCutShortComplex P K a b hab).map (eval _ _ n)).Splitting :=
  cochainTensorShortComplexRightSplitting (intervalCutShortComplex P a b hab)
    (intervalCutSplitting P a b hab) K n

/-- 概要：全テンソル後の任意区間は短完全。
方針：次数ごとの分裂を用いる。
規約：係数複体の平坦性は不要。使われ方：KST Lemma 4.10 の cone–商比較。 -/
theorem intervalTensorCutShortComplex_shortExact
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) (hab : b ≤ a) :
    (intervalTensorCutShortComplex P K a b hab).ShortExact :=
  cochainTensorShortComplexRight_shortExact (intervalCutShortComplex P a b hab)
    (intervalCutSplitting P a b hab) K

/-- 概要：再添字したテンソル項濾過の射に、その実際の商短複体を割り当てる。
方針：再添字関手が与える下端をそのまま使う。
規約：Koszul の有限添字への制限を含む。使われ方：KST Lemma 4.10 の微分比較。 -/
def tensorFiltrationInterval {I : Type v} [Preorder I]
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (index : I ⥤ ℤ)
    {i j : I} (f : i ⟶ j) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  intervalTensorCutShortComplex P K (-index.obj i) (-index.obj j)
    (neg_le_neg (index.map f).le)

/-- 概要：実際の再添字項濾過の δ を区間の分裂境界と左の商射で表す。
方針：各区間の実際の第一射を用いて、一般の濾過連結写像公式を適用する。
規約：任意の単調再添字、任意の係数複体。使われ方：KST Lemma 4.10 の有限濾過の初頁微分。 -/
theorem tensorFiltration_delta_split {I : Type v} [Preorder I]
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (index : I ⥤ ℤ)
    {i j k : I} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ) :
    let F := index ⋙ truncationFiltration P ⋙ tensorRight K
    let S := tensorFiltrationInterval P K index f
    let T := tensorFiltrationInterval P K index g
    (filteredHomologySpectralObject F).δ f g n (n + 1) rfl ≫
      (filtrationIntervalHomologyIso F f (n + 1)).hom ≫
        homologyMap (CochainComplex.mappingCone.descShortComplex S) (n + 1) =
      (filtrationIntervalHomologyIso F g n).hom ≫
        homologyMap (CochainComplex.mappingCone.descShortComplex T) n ≫
          (homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftMap
            (CochainComplex.homOfDegreewiseSplit T
              (intervalTensorCutSplitting P K (-index.obj j) (-index.obj k)
                (neg_le_neg (index.map g).le))) n (n + 1) (by omega) ≫
            homologyMap S.g (n + 1) := by
  let F := index ⋙ truncationFiltration P ⋙ tensorRight K
  let S := tensorFiltrationInterval P K index f
  let T := tensorFiltrationInterval P K index g
  have hf : F.map f ≫ S.g = 0 := S.zero
  have hg : F.map g ≫ T.g = 0 := T.zero
  have hT : (ShortComplex.mk (F.map g) T.g hg).ShortExact :=
    intervalTensorCutShortComplex_shortExact P K (-index.obj j) (-index.obj k)
      (neg_le_neg (index.map g).le)
  exact filtrationInterval_delta_split F f g S.g T.g hf hg hT
    (intervalTensorCutSplitting P K (-index.obj j) (-index.obj k)
      (neg_le_neg (index.map g).le)) n

/-- 概要：再添字テンソル濾過の区間ホモロジーを、実際の商のホモロジーへ同定する。
方針：cone への比較に、次数ごと分裂する短完全列の商比較の擬同型を続ける。
規約：比較射自体は標準の cone から商への射。
使われ方：KST Lemma 4.10 の初頁の商モデル。 -/
def tensorFiltrationIntervalHomologyIso {I : Type v} [Preorder I]
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (index : I ⥤ ℤ)
    {i j : I} (f : i ⟶ j) (n : ℤ) :
    ((filteredHomologySpectralObject (index ⋙ truncationFiltration P ⋙ tensorRight K)).H n).obj
      (ComposableArrows.mk₁ f) ≅ (tensorFiltrationInterval P K index f).X₃.homology n := by
  let S := tensorFiltrationInterval P K index f
  let : QuasiIso (CochainComplex.mappingCone.descShortComplex S) :=
    CochainComplex.mappingCone.quasiIso_descShortComplex
      (intervalTensorCutShortComplex_shortExact P K (-index.obj i) (-index.obj j)
        (neg_le_neg (index.map f).le))
  exact filtrationIntervalHomologyIso _ f n ≪≫
    isoOfQuasiIsoAt (CochainComplex.mappingCone.descShortComplex S) n

/-- 概要：商ホモロジーの同型で濾過の δ を移すと分裂境界と左の商射になる。
方針：区間同型の定義を展開して、実際の濾過に対する境界公式を適用する。
規約：商ホモロジー同型に逆射の選択を持ち込まない。
使われ方：KST Lemma 4.10 の初頁微分を射の等式として比較する。 -/
theorem tensorFiltration_delta_quotientIso {I : Type v} [Preorder I]
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (index : I ⥤ ℤ)
    {i j k : I} (f : i ⟶ j) (g : j ⟶ k) (n n' : ℤ) (hn : n + 1 = n') :
    let F := index ⋙ truncationFiltration P ⋙ tensorRight K
    let S := tensorFiltrationInterval P K index f
    let T := tensorFiltrationInterval P K index g
    (filteredHomologySpectralObject F).δ f g n n' hn ≫
      (tensorFiltrationIntervalHomologyIso P K index f n').hom =
      (tensorFiltrationIntervalHomologyIso P K index g n).hom ≫
        (homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftMap
          (CochainComplex.homOfDegreewiseSplit T
            (intervalTensorCutSplitting P K (-index.obj j) (-index.obj k)
              (neg_le_neg (index.map g).le))) n n' (by omega) ≫
          homologyMap S.g n' := by
  obtain rfl := hn
  exact tensorFiltration_delta_split P K index f g n

end SerrePositivity.KST.ProExcision
