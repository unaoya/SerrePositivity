module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.QCatPullbackLimit

/-!
概要：可逆 path で置換した任意の cospan の Cat_∞ 内の実際の極限錐。
方針：置換後の終点関手の右持ち上げ条件を QCat の豊穣極限判定へ適用する。
規約：元の p、q の図式への輸送は別工程。錐の頂点は既存の catPullbackObject p q。
使われ方：Cat_∞ の任意の引き戻しを元の図式へ戻す比較の出発点。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]

/-- 概要：任意の cospan の第一関手を可逆 path で置換した QCat の図式。
方針：置換した始域・元の第二始域・底を QCat に束縛し、終点関手で cospan を作る。
規約：置換した第一関手を使うことを図式の型に明示する。
使われ方：Cat_∞ の極限性を先に検証できる図式。 -/
def catPullbackReplacementDiagram (p : A ⟶ C) (q : B ⟶ C) :
    AsSmall.{u} WalkingCospan ⥤ QCat.{u} :=
  let E₀ : QCat.{u} := (⟨equivalencePathReplacement p, inferInstance⟩ : QuasicategoryObject.{u})
  let B₀ : QCat.{u} := (⟨B, inferInstance⟩ : QuasicategoryObject.{u})
  let C₀ : QCat.{u} := (⟨C, inferInstance⟩ : QuasicategoryObject.{u})
  qCatPullbackDiagram (show E₀ ⟶ C₀ from equivalencePathReplacementMap p) (show B₀ ⟶ C₀ from q)

/-- 概要：path 置換後の cospan の厳密な引き戻し錐。
方針：置換後の終点関手と元の第二関手に QCat の通常の引き戻し錐を適用する。
規約：頂点の台の単体集合は既存の catPullback p q。
使われ方：coherent nerve に写す実際の錐。 -/
def catPullbackReplacementOrdinaryCone (p : A ⟶ C) (q : B ⟶ C) :
    Cone (catPullbackReplacementDiagram p q) :=
  let E₀ : QCat.{u} := (⟨equivalencePathReplacement p, inferInstance⟩ : QuasicategoryObject.{u})
  let B₀ : QCat.{u} := (⟨B, inferInstance⟩ : QuasicategoryObject.{u})
  let C₀ : QCat.{u} := (⟨C, inferInstance⟩ : QuasicategoryObject.{u})
  qCatPullbackCone (show E₀ ⟶ C₀ from equivalencePathReplacementMap p) (show B₀ ⟶ C₀ from q)

/-- 概要：path 置換した cospan の Cat_∞ 内の native な錐。
方針：QCat の厳密な錐を coherent nerve の join 錐にする。
規約：極限性は次の補題で証明し、データのフィールドとして仮定しない。
使われ方：元の cospan の極限錐へ輸送する対象。 -/
def catPullbackReplacementCone (p : A ⟶ C) (q : B ⟶ C) :
    JoinCone (HomotopyLimits.strictCoherentDiagram (catPullbackReplacementDiagram p q)) :=
  HomotopyLimits.strictCoherentCone (catPullbackReplacementOrdinaryCone p q)

/-- 概要：path 置換した任意の cospan の native な錐は Cat_∞ の極限錐。
方針：全ての QCat 対象からの豊穣 Hom の極限性と一脚の fibration 性を使う。
規約：元の関手 p、q に fibration 性は要求しない。
使われ方：任意の cospan の ∞ 引き戻しを存在させる置換の段階。 -/
lemma catPullbackReplacementCone_isLimit (p : A ⟶ C) (q : B ⟶ C) :
    IsLimitCone (catPullbackReplacementCone p q) := by
  dsimp only [catPullbackReplacementCone, catPullbackReplacementOrdinaryCone]
  exact qCatPullbackInfinityCone_isLimit _ _
    (F1B.kanEquivalenceLifting_equivalencePathReplacementMap p)

/-- 概要：path 置換後の native な極限錐の頂点は既存の引き戻し候補。
方針：厳密な錐の頂点の公式と引き戻し対象の束縛の定義を計算する。
規約：頂点は同値だけでなく厳密に一致する。
使われ方：候補の全試験関手 core の比較と実際の極限錐の接続。 -/
lemma catPullbackReplacementCone_vertex (p : A ⟶ C) (q : B ⟶ C) :
    (catPullbackReplacementCone p q).vertex = coherentVertex (catPullbackObject p q) :=
  HomotopyLimits.strictCoherentCone_vertex _

end SerrePositivity.InfinityCategories.F2
