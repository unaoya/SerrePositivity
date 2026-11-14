module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.BigCechSitePresentation
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.BigCechAlexander

/-!
# 既存の BigCechAlexander の site 上の組み立て

## 概要
大きい枠の選択を site 上の余単体的対象にし、環の既存の構造射との一致を示す。

## 方針
既存の変数の普遍性を共通の組み立てへ入力し、map_unique で環射を照合する。

## 規約
BS 著者版 Construction 4.17–4.18。有限枠との比較は使わない。

## 使われ方
既存の BigCechAlexander の弱始性、標準余積と Čech データ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity.BhattScholze.Prismatic
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {Q : Poly (A ⧸ P.ideal)} {κ : Cardinal.{u}}
variable (E : ∀ n, BigCechTerm P Q n) (hb : ∀ n, IsBoundedPrism (E n).prism)
variable (hs : ∀ n, Cardinal.mk (E n).carrier ≤ κ)

/-- 大きい枠の既存の包絡から作る site の余単体的対象。 -/
def bigCechSiteAlexander : CosimplicialObject (PrismOver P (polyCompletion P Q.n) κ) :=
  CechAlexanderPresentation.cosimplicial (fun n => (E n).sitePresentation (hb n) (hs n))

/-- 概要：site の構造射の台環射は既存の BigCechTerm.map と一致する。
方針：既存の map_unique を変数上の一致に適用する。
規約：BS 著者版 Construction 4.18。使われ方：既存の bigCechAlexander との照合。 -/
theorem bigCechSiteAlexander_map {m n : SimplexCategory} (θ : m ⟶ n) :
    ((bigCechSiteAlexander E hb hs).map θ).toHom.toRingHom =
      (E m.len).map (E n.len) (𝟙 Q) θ.toOrderHom := by
  let f := (bigCechSiteAlexander E hb hs).map θ
  apply (E m.len).map_unique (E n.len) (𝟙 Q) θ.toOrderHom f.toHom.toRingHom f.toHom.map_delta
  · exact congrArg OrientedPrism.Hom.toRingHom f.comm_base
  · intro s
    have h := CechAlexanderPresentation.map_variable
      ((E m.len).sitePresentation (hb _) (hs _))
      ((E n.len).sitePresentation (hb _) (hs _)) θ.toOrderHom s
    change f.toHom.toRingHom ((E m.len).variableImage s) =
      (E n.len).variableImage (s.1, θ.toOrderHom s.2) at h
    have he : BigCechTerm.indexMap (𝟙 Q) θ.toOrderHom s = (s.1, θ.toOrderHom s.2) := by
      simp only [BigCechTerm.indexMap, polyCompletionMap_id, AlgHom.id_apply]
    rw [he]
    exact h

/-- 大きい枠の零次の site 対象は環の向きで弱始。 -/
theorem bigCechSiteAlexander_weaklyInitial :
    CategoryTheory.IsWeaklyInitial ((bigCechSiteAlexander E hb hs).obj ⦋0⦌) :=
  ((E 0).sitePresentation (hb 0) (hs 0)).weaklyInitial

/-- 大きい枠の標準頂点による n 次項の余積。 -/
def bigCechSiteAlexander_isCoproduct (n : ℕ) :
    IsColimit (Cofan.mk ((bigCechSiteAlexander E hb hs).obj ⦋n⦌)
      (fun i : Fin (n + 1) => (bigCechSiteAlexander E hb hs).map
        (SimplexCategory.const ⦋0⦌ ⦋n⦌ i))) :=
  CechAlexanderPresentation.isCoproduct (fun n => (E n).sitePresentation (hb n) (hs n)) n

/-- 大きい枠の Čech 余積を site の積として読むデータ。 -/
def bigCechSiteNerve : CategoryTheory.CechNerveData
    (Opposite.op ((bigCechSiteAlexander E hb hs).obj ⦋0⦌)) :=
  CategoryTheory.CechNerveData.ofCoproducts (bigCechSiteAlexander E hb hs)
    (bigCechSiteAlexander_isCoproduct E hb hs)

end SerrePositivity.BhattScholze.Prismatic
