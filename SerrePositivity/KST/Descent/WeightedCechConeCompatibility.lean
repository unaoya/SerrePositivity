module

public import SerrePositivity.KST.Descent.WeightedCechFubini

/-!
# 重みつき Fubini と指定錐の随伴対応の整合性

## 概要
構成した錐空間の Fubini 同型が、元の指定錐の随伴像・単位・余単位を保つことを示す。

## 方針
右随伴の一意性の同型の単位の公式と自然性を、左随伴の結合子に沿って移す。

## 規約
任意の自然同型の存在ではなく、WeightedCechFubini の指定同型そのものについて述べる。
導来比較と指定増強への移送は別に接続する。

## 使われ方
論文 補題 3.2・3.3 の Čech の指定増強との Fubini の整合性への入力。
-/

@[expose] public section

noncomputable section

universe u v w t

open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DiagramModel

namespace SerrePositivity.KST.Descent

/-- 概要：右随伴の指定一意同型は同じ錐の随伴像を保つ（論文 補題 3.2）。
方針：単位の比較の公式と自然性を使う。
規約：同じ左随伴の同じ射を比較する。使われ方：重みつき Fubini の指定錐の保持。 -/
theorem cechConeMate_rightAdjointUniq
    {C : Type u} [Category.{v} C] {D : Type w} [Category.{t} D]
    {F : C ⥤ D} {R R' : D ⥤ C} (a : F ⊣ R) (b : F ⊣ R')
    {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    (a.homEquiv X Y f) ≫ (a.rightAdjointUniq b).hom.app Y = b.homEquiv X Y f := by
  simp only [Adjunction.homEquiv_unit]
  rw [Category.assoc, (a.rightAdjointUniq b).hom.naturality f,
    ← Category.assoc, Adjunction.unit_rightAdjointUniq_hom_app]

variable (K L : Type u) [SmallCategory K] [SmallCategory L]
  (W : K ⥤ SSet.{u}) (V : L ⥤ SSet.{u})

/-- 概要：指定重みつき Fubini は元の錐の随伴像を保持（論文 補題 3.2・3.3）。
方針：指定右随伴同型の随伴像の保持と、左随伴の結合子への移送を合成する。
規約：比較する錐は指定テンソル結合子だけで移す。
使われ方：増強から得る Čech 比較を Fubini へ渡す。 -/
theorem weightedCechFubiniIso_mate (X : SSet.{u}) (F : K × L ⥤ SSet.{u})
    (f : (WeightedCones.tensorDiagram (K × L) (externalCechWeight K L W V)).obj X ⟶ F) :
    ((WeightedCones.adjunction (K × L) (externalCechWeight K L W V)).homEquiv X F f) ≫
        (weightedCechFubiniIso K L W V).hom.app F =
      (iteratedCechConeAdjunction K L W V).homEquiv X F
        ((externalCechTensorIso K L W V).inv.app X ≫ f) := by
  exact (cechConeMate_rightAdjointUniq
    (WeightedCones.adjunction (K × L) (externalCechWeight K L W V))
    ((iteratedCechConeAdjunction K L W V).ofNatIsoLeft
      (externalCechTensorIso K L W V).symm) f).trans
      (Adjunction.homEquiv_ofNatIsoLeft_apply _ _ _)

/-- 概要：指定重みつき Fubini の単位は結合子と整合（論文 補題 3.2）。
方針：右随伴同型の単位の公式を指定された左随伴の同型に適用する。
規約：実際の単位射についての等式。使われ方：指定増強比較の正規化。 -/
theorem weightedCechFubiniIso_unit (X : SSet.{u}) :
    (WeightedCones.adjunction (K × L) (externalCechWeight K L W V)).unit.app X ≫
        (weightedCechFubiniIso K L W V).hom.app
          ((WeightedCones.tensorDiagram (K × L) (externalCechWeight K L W V)).obj X) =
      (iteratedCechConeAdjunction K L W V).unit.app X ≫
        (iteratedCechConeSpace K L W V).map ((externalCechTensorIso K L W V).inv.app X) :=
  Adjunction.unit_rightAdjointUniq_hom_app
    (WeightedCones.adjunction (K × L) (externalCechWeight K L W V))
    ((iteratedCechConeAdjunction K L W V).ofNatIsoLeft (externalCechTensorIso K L W V).symm) X

/-- 概要：指定重みつき Fubini の余単位も結合子と整合（論文 補題 3.2）。
方針：右随伴同型の余単位の公式を指定された左随伴の同型に適用する。
規約：指定錐の評価射を保持する。使われ方：導来した指定錐の比較。 -/
theorem weightedCechFubiniIso_counit (F : K × L ⥤ SSet.{u}) :
    (WeightedCones.tensorDiagram (K × L) (externalCechWeight K L W V)).map
        ((weightedCechFubiniIso K L W V).hom.app F) ≫
      ((externalCechTensorIso K L W V).hom.app ((iteratedCechConeSpace K L W V).obj F) ≫
        (iteratedCechConeAdjunction K L W V).counit.app F) =
      (WeightedCones.adjunction (K × L) (externalCechWeight K L W V)).counit.app F :=
  Adjunction.rightAdjointUniq_hom_app_counit
    (WeightedCones.adjunction (K × L) (externalCechWeight K L W V))
    ((iteratedCechConeAdjunction K L W V).ofNatIsoLeft (externalCechTensorIso K L W V).symm) F

end SerrePositivity.KST.Descent
