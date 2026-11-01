module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ModelCompatibility
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.BoundaryOne

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
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
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

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma restriction_trivialFibration {V T P : SSet.{v}} (i : V ⟶ T) [Mono i]
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p) :
    trivialFibrations SSet.{v} ((MonoidalClosed.internalHom.map i.op).app P) := by
  have : Quillen.HasQuillenPullbackHom (MonoidalClosed.internalHom (C := SSet.{v})) :=
    simplicial_SM7 hcof hfib
  have hi : Cofibration i := by rw [cofibration_iff, hcof]; infer_instance
  have : Fibration p := ⟨hp.1⟩
  have : WeakEquivalence p := ⟨hp.2⟩
  let sq := Functor.PullbackObjObj.ofIsTerminal MonoidalClosed.internalHom i p
    SSet.stdSimplex.isTerminalObj₀
  have := Quillen.HasQuillenPullbackHom.fibration i p sq hi inferInstance
  have := Quillen.HasQuillenPullbackHom.weakEquivalence i p sq hi inferInstance
    (Or.inr inferInstance)
  exact ⟨mem_fibrations sq.π, mem_weakEquivalences sq.π⟩

include hcof hfib in
lemma projection_trivialFibration {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p) : trivialFibrations SSet.{v} (projection i b) :=
  (trivialFibrations SSet.{v}).of_isPullback (IsPullback.of_hasPullback _ _)
    (restriction_trivialFibration hcof hfib i p hp)

include hcof hfib in
lemma kanComplex {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p) : SSet.KanComplex (obj i b) := by
  have : IsFibrant (obj i b) :=
    (isFibrant_iff_of_isTerminal (projection i b) SSet.stdSimplex.isTerminalObj₀).mpr
      ⟨(projection_trivialFibration hcof hfib i b p hp).1⟩
  apply (SSet.modelCategoryQuillen.fibration_iff (terminal.from (obj i b))).mpr
  rw [← hfib]
  exact mem_fibrations _

include hcof hfib in
lemma extension {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p) {K L : SSet.{v}} (j : K ⟶ L) [Mono j]
    (a : K ⟶ obj i b) : ∃ e : L ⟶ obj i b, j ≫ e = a := by
  have hj : cofibrations SSet.{v} j := by rw [hcof]; infer_instance
  have : HasLiftingProperty j (projection i b) := MorphismProperty.hasLiftingProperty_of_wfs _ _
    hj (projection_trivialFibration hcof hfib i b p hp)
  let sq : CommSq a j (projection i b) (SSet.stdSimplex.isTerminalObj₀.from L) :=
    ⟨SSet.stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

include hcof hfib in
lemma interval {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p)
    (s t : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ obj i b) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ obj i b,
      SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫ e = s ∧
      SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫ e = t := by
  let a := HomotopyFunctionComplex.BoundaryOne.isColimit.desc (BinaryCofan.mk s t)
  obtain ⟨e, he⟩ := extension hcof hfib i b p hp (SSet.boundary 1).ι a
  refine ⟨e, ?_, ?_⟩
  · change SSet.stdSimplex.δ (1 : Fin 2) ≫ e = s
    rw [← SSet.boundary.ι_ι (1 : Fin 2), Category.assoc, he]
    exact HomotopyFunctionComplex.BoundaryOne.isColimit.fac (BinaryCofan.mk s t) ⟨WalkingPair.left⟩
  · change SSet.stdSimplex.δ (0 : Fin 2) ≫ e = t
    rw [← SSet.boundary.ι_ι (0 : Fin 2), Category.assoc, he]
    exact HomotopyFunctionComplex.BoundaryOne.isColimit.fac (BinaryCofan.mk s t) ⟨WalkingPair.right⟩

include hcof hfib in
/-- Any two extensions are joined by an actual simplicial homotopy relative to V. -/
lemma relative_homotopy {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p) (e₀ e₁ : T ⟶ P) (h₀ : i ≫ e₀ = b) (h₁ : i ≫ e₁ = b) :
    ∃ H : T ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ P,
      T ◁ SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫ H =
        T ◁ pointUnitIso.hom ≫ (ρ_ T).hom ≫ e₀ ∧
      T ◁ SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫ H =
        T ◁ pointUnitIso.hom ≫ (ρ_ T).hom ≫ e₁ ∧
      i ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ≫ H =
        V ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫ pointUnitIso.hom) ≫ (ρ_ V).hom ≫ b := by
  obtain ⟨e, hs, ht⟩ := interval hcof hfib i b p hp (ofExtension i b e₀ h₀) (ofExtension i b e₁ h₁)
  refine ⟨family i b e, ?_, ?_, family_fixed_boundary i b e⟩
  · rw [← family_naturality, hs, family_ofExtension]
  · rw [← family_naturality, ht, family_ofExtension]

include hcof hfib in
lemma nonempty_fixedBoundaryHomotopy {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p) (e₀ e₁ : T ⟶ P) (h₀ : i ≫ e₀ = b) (h₁ : i ≫ e₁ = b) :
    Nonempty (FixedBoundaryHomotopy i b e₀ e₁) := by
  obtain ⟨H, h₀, h₁, hb⟩ := relative_homotopy hcof hfib i b p hp e₀ e₁ h₀ h₁
  exact ⟨⟨H, h₀, h₁, hb⟩⟩

end SerrePositivity.SimplicialModel.RelativeChoiceSpace
