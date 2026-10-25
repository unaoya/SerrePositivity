module

public import SerrePositivity.InfinityCategories.F2.Presentable.FunctorHomTensor

/-!
概要：二つの元の全単位候補を直積の全単位候補へまとめる。
方針：二つの射影への制限を全関手圏の積の Hom 全単射で戻す。
規約：単位の普遍性や随伴の存在を入力せず、元の二胞体を保持する。
使われ方：積の反映模型の全随伴の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：二つの全単位の射影への制限を同じ直積の両成分として束ねる。
方針：元の二つの単位を第一・第二射影で前合成する。
規約：元の全二胞体の前合成を使う。
使われ方：直積の単位候補の成分表示。 -/
def tensorUnitHomComponents {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ X} {G : Y ⟶ Y} (η : FunctorHom (𝟙 X) F) (ε : FunctorHom (𝟙 Y) G) :
    FunctorHom ((𝟙 (X ⊗ Y)) ≫ fst X Y) ((F ⊗ₘ G) ≫ fst X Y) ×
      FunctorHom ((𝟙 (X ⊗ Y)) ≫ snd X Y) ((F ⊗ₘ G) ≫ snd X Y) := by
  constructor
  · change FunctorHom (fst X Y) (fst X Y ≫ F)
    exact (hoFunctor.map ((pre (fst X Y)).app X)).toFunctor.map η
  · change FunctorHom (snd X Y) (snd X Y ≫ G)
    exact (hoFunctor.map ((pre (snd X Y)).app Y)).toFunctor.map ε

/-- 概要：二つの元の全単位候補から直積の全単位候補を構成する。
方針：全関手圏の射の積分解の逆を取る。
規約：各点ごとの選択や新しい全単位の存在仮定は使わない。
使われ方：直積の全随伴の単位。 -/
def tensorUnitHom {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ X} {G : Y ⟶ Y} (η : FunctorHom (𝟙 X) F) (ε : FunctorHom (𝟙 Y) G) :
    FunctorHom (𝟙 (X ⊗ Y)) (F ⊗ₘ G) :=
  (functorHomTensorEquiv _ _).symm (tensorUnitHomComponents η ε)

/-- 概要：構成した全単位の成分分解は元の二つの単位の制限そのもの。
方針：全 Hom 全単射の逆の恒等式を使う。
規約：元の二胞体を等式で回収する。
使われ方：単位 Hom 比較を成分ごとへ戻す。 -/
lemma tensorUnitHom_components {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ X} {G : Y ⟶ Y} (η : FunctorHom (𝟙 X) F) (ε : FunctorHom (𝟙 Y) G) :
    functorHomTensorEquiv (𝟙 (X ⊗ Y)) (F ⊗ₘ G) (tensorUnitHom η ε) =
      tensorUnitHomComponents η ε :=
  (functorHomTensorEquiv _ _).apply_symm_apply _

end SerrePositivity.InfinityCategories.F2.Presentable
