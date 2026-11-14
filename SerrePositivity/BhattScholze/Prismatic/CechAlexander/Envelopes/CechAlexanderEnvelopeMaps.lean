module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.CechAlexanderAssembly
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Complexes.CechAlexanderFreeDelta

/-!
# Čech–Alexander の site の射と包絡の始域の比較

## 概要
変数の普遍性から作った site の構造射が、原典の完備自由 δ 環の構造射を延長することを示す。

## 方針
変数上の式と基底上の可換性から、完備自由 δ 環の射の一意性を使う。

## 規約
BS 著者版 Construction 4.18。選んだ実際の包絡の単位を保つ比較。

## 使われ方
後の係数変更や包絡の比較で同じ余単体的構造を使うための入力。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity.BhattScholze.Prismatic
open CategoryTheory
open scoped Simplicial
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (R : Type u) [CommRing R] [Algebra (A ⧸ P.ideal) R]
variable (h : HasEnvelopes P R) (κ : Cardinal.{u}) (hκ : cutoff A R ≤ κ)

/-- 概要：site の単体射は包絡の初期変数をその添字の変数へ送る。
方針：共通の Presentation の変数の式を適用する。
規約：BS 著者版 Construction 4.18。使われ方：包絡の始域の構造射との照合。 -/
theorem cechAlexanderMap_variable {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (s : cechIndex R m) :
    ((cechAlexander P R h κ hκ).map θ).toHom.toRingHom
      ((HasEnvelopes.term P R h m).variableImage s) =
        (HasEnvelopes.term P R h n).variableImage (cechIndexMap R θ s) :=
  CechAlexanderPresentation.map_variable
    ((HasEnvelopes.term P R h m).sitePresentation κ hκ)
    ((HasEnvelopes.term P R h n).sitePresentation κ hκ) θ.toOrderHom s

/-- 概要：site の構造射は完備自由 δ 環の構造射を包絡の単位に沿って延長する。
方針：基底と初期変数で両辺を比較し、完備自由 δ 環の外延性を使う。
規約：BS 著者版 Construction 4.18。使われ方：実際の包絡による余単体的構成の確認。 -/
theorem cechAlexanderMap_unit {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (((cechAlexander P R h κ hκ).map θ).toHom.toRingHom).comp
        (HasEnvelopes.term P R h m).unit =
      ((HasEnvelopes.term P R h n).unit).comp (cechFreeDeltaMap P R θ) := by
  let E := HasEnvelopes.term P R h m
  let F := HasEnvelopes.term P R h n
  let f := (cechAlexander P R h κ hκ).map θ
  apply completedFreeDeltaHom_ext P _ F.prism.deltaStructure F.base.toRingHom F.base.map_delta
    F.prism.complete_p F.base.isModuleComplete_map_generator
    (f.toHom.map_delta.comp E.isEnvelope.isDeltaHom)
    (F.isEnvelope.isDeltaHom.comp (cechFreeDeltaMap_isDeltaHom P R θ))
  · rw [RingHom.comp_assoc]
    exact congrArg OrientedPrism.Hom.toRingHom f.comm_base
  · rw [RingHom.comp_assoc, cechFreeDeltaMap_base]
    rfl
  · intro s
    change f.toHom.toRingHom (E.variableImage s) =
      F.unit (cechFreeDeltaMap P R θ (completedFreeDeltaVariable P _ s))
    rw [cechFreeDeltaMap_variable]
    exact cechAlexanderMap_variable P R h κ hκ θ s

end SerrePositivity.BhattScholze.Prismatic
