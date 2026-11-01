module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# 境界を固定した延長の写像空間

## 概要
内部Homの制限のファイバーで固定境界上の延長とその族を表す。
任意モデル源の厳密化から独立して利用できる一般道具である。

## 方針（定義・証明）
pullbackで写像空間を定義し、指定モデルのSM7から相対延長を導く。
既存の構成を同じ公開名と証明のまま一般層に切り出す。

## 規約と注意
宇宙と仮定は各宣言に明示したものを用いる。
専用の比較図式・正規化充填・選択の整合性は仮定しない。

## 使われ方
一般入口GeneralToolsおよび共有Foundationsから利用する。
旧パスの互換importを通して中断中の厳密化からも利用する。
今後のS-構成・ホモトピー比較・局所化の基礎として使える。
詳細はformalization-plans/archive/k-theory-generalization-inventory.mdの配置実施記録を参照。
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.RelativeChoiceSpace

abbrev pointUnitIso : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ≅ 𝟙_ SSet.{v} :=
  SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit

abbrev name {V P : SSet.{v}} (b : V ⟶ P) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ (ihom V).obj P :=
  pointUnitIso.hom ≫ curry' b

lemma name_precomp {V T P : SSet.{v}} (i : V ⟶ T) (e : T ⟶ P) :
    name e ≫ (MonoidalClosed.internalHom.map i.op).app P = name (i ≫ e) := by
  have h : curry' e ≫ (pre i).app P = curry' (i ≫ e) := by
    dsimp only [curry']
    rw [curry_pre_app]
    congr 1
  exact (Category.assoc _ _ _).trans (congrArg (fun k => pointUnitIso.hom ≫ k) h)

/-- 指定した境界写像を延長する写像の空間をpullbackで表す。
境界の包含に単射性はこの定義では要求せず、内部Homの制限の指定点上のファイバーを取る。 -/
abbrev obj {V T P : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P) : SSet.{v} :=
  pullback ((MonoidalClosed.internalHom.map i.op).app P) (name b)

abbrev inclusion {V T P : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P) :
    obj i b ⟶ (ihom T).obj P := pullback.fst _ _

abbrev projection {V T P : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P) :
    obj i b ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) := pullback.snd _ _

@[reassoc]
lemma over {V T P : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P) :
    inclusion i b ≫ (MonoidalClosed.internalHom.map i.op).app P =
      projection i b ≫ name b := pullback.condition

def ofExtension {V T P : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P)
    (e : T ⟶ P) (he : i ≫ e = b) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ obj i b :=
  pullback.lift (name e) (𝟙 _) (by rw [name_precomp, he, Category.id_comp])

@[reassoc (attr := simp)]
lemma ofExtension_inclusion {V T P : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P)
    (e : T ⟶ P) (he : i ≫ e = b) :
    ofExtension i b e he ≫ inclusion i b = name e := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma ofExtension_projection {V T P : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P)
    (e : T ⟶ P) (he : i ≫ e = b) :
    ofExtension i b e he ≫ projection i b = 𝟙 _ := pullback.lift_snd _ _ _

/-- A parameter simplex gives an actual family T⊗K→P of extensions. -/
abbrev family {V T P K : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P) (s : K ⟶ obj i b) :
    T ⊗ K ⟶ P := uncurry (s ≫ inclusion i b)

lemma family_naturality {V T P K L : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P)
    (s : K ⟶ obj i b) (u : L ⟶ K) :
    family i b (u ≫ s) = T ◁ u ≫ family i b s := by
  rw [family, Category.assoc, uncurry_natural_left]

/-- The prescribed boundary is fixed along the entire parameter, not only its vertices. -/
lemma family_boundary {V T P K : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P) (s : K ⟶ obj i b) :
    i ▷ K ≫ family i b s = uncurry (s ≫ projection i b ≫ name b) := by
  rw [← uncurry_pre_app]
  congr 1
  rw [Category.assoc]
  exact congrArg (fun k => s ≫ k) (over i b)

lemma family_ofExtension {V T P : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P)
    (e : T ⟶ P) (he : i ≫ e = b) :
    family i b (ofExtension i b e he) = T ◁ pointUnitIso.hom ≫ (ρ_ T).hom ≫ e := by
  rw [family, ofExtension_inclusion, name, uncurry_natural_left]
  dsimp only [curry']
  rw [uncurry_curry]

lemma family_fixed_boundary {V T P K : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P)
    (s : K ⟶ obj i b) :
    i ▷ K ≫ family i b s =
      V ◁ (SSet.stdSimplex.isTerminalObj₀.from K ≫ pointUnitIso.hom) ≫ (ρ_ V).hom ≫ b := by
  have hp : s ≫ projection i b = SSet.stdSimplex.isTerminalObj₀.from K :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [family_boundary, ← Category.assoc, hp, name, ← Category.assoc, uncurry_natural_left]
  dsimp only [curry']
  rw [uncurry_curry]

/-- An actual interval family with both endpoints and its whole fixed boundary. -/
structure FixedBoundaryHomotopy {V T P : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P)
    (e₀ e₁ : T ⟶ P) where
  hom : T ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ P
  at_zero : T ◁ SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫ hom =
    T ◁ pointUnitIso.hom ≫ (ρ_ T).hom ≫ e₀
  at_one : T ◁ SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫ hom =
    T ◁ pointUnitIso.hom ≫ (ρ_ T).hom ≫ e₁
  relative : i ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ≫ hom =
    V ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫ pointUnitIso.hom) ≫ (ρ_ V).hom ≫ b

end SerrePositivity.SimplicialModel.RelativeChoiceSpace
