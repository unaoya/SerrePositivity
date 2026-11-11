module

public import Mathlib.CategoryTheory.Localization.Opposite
public import Mathlib.CategoryTheory.Yoneda

/-!
# 局所化の手前の表現可能 Hom 同型から対象の同型を復元する

概要：Hovey §1.3 の局所化に沿って表現可能 Hom の同型を降ろす。
方針：局所化による前合成と Yoneda の二つの充満忠実性を使う。
規約：モデル構造は仮定せず、同じ Hom 同型の成分を保持する。
使われ方：異なる frame で計算した極限の比較。
-/

@[expose] public section

noncomputable section

universe u v w

namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

open CategoryTheory Opposite

variable {C : Type u} [Category C] {H : Type v} [Category.{w} H]
  (Q : C ⥤ H) (W : MorphismProperty C) [Q.IsLocalization W]
  {X Y : H}

/-- 概要：制限した表現可能 Hom 同型から対象の同型を復元（Hovey §1.3）。
方針：同じ反対局所化の前合成から復元し、Yoneda の充満忠実性を使う。
規約：与えられた成分を保持する。
使われ方：右導来極限の異なる具体的計算対象の比較。 -/
def comparisonIso (e : Q.op ⋙ yoneda.obj X ≅ Q.op ⋙ yoneda.obj Y) : X ≅ Y :=
  Yoneda.fullyFaithful.preimageIso
    ((Localization.fullyFaithfulWhiskeringLeft Q.op W.op (Type w)).preimageIso
      (X := yoneda.obj X) (Y := yoneda.obj Y) e)

/-- 概要：復元した同型の後合成は元の Hom 同型の成分（Hovey §1.3）。
方針：二つの preimage の射の計算式を同じ元の対象で評価する。
規約：元の局所化像からの任意の射に対する式。
使われ方：元の通常錐からの比較射の保存。 -/
lemma comparisonIso_hom_app (e : Q.op ⋙ yoneda.obj X ≅ Q.op ⋙ yoneda.obj Y)
    (Z : C) (f : Q.obj Z ⟶ X) :
    f ≫ (comparisonIso Q W e).hom = (e.hom.app (op Z)) f := by
  let hQ := Localization.fullyFaithfulWhiskeringLeft Q.op W.op (Type w)
  let e' := hQ.preimageIso (X := yoneda.obj X) (Y := yoneda.obj Y) e
  have h₁ := congr_app (hQ.map_preimage e.hom) (op Z)
  have h₂ := congr_app (Yoneda.fullyFaithful.map_preimage e'.hom) (op (Q.obj Z))
  exact ConcreteCategory.congr_hom (h₂.trans h₁) f

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
