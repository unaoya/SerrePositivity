module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryOne
public import SerrePositivity.HomotopicalAlgebra.Simplicial.FixedBoundaryExtensions
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ModelCompatibility

/-!
分割で生成：docstring を書き直すこと
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

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma restriction_trivialFibration {V T P : SSet.{v}} (i : V ⟶ T) [Mono i]
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p) :
    trivialFibrations SSet.{v} ((MonoidalClosed.internalHom.map i.op).app P) := by
  have : Quillen.HasQuillenPullbackHom (MonoidalClosed.internalHom (C := SSet.{v})) :=
    _root_.SerrePositivity.SimplicialModel.simplicial_SM7 hcof hfib
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
    (hp : trivialFibrations SSet.{v} p) : trivialFibrations SSet.{v} (_root_.SerrePositivity.SimplicialModel.RelativeChoiceSpace.projection i b) :=
  (trivialFibrations SSet.{v}).of_isPullback (IsPullback.of_hasPullback _ _)
    (restriction_trivialFibration hcof hfib i p hp)

include hcof hfib in
lemma kanComplex {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p) : SSet.KanComplex (_root_.SerrePositivity.SimplicialModel.RelativeChoiceSpace.obj i b) := by
  have : IsFibrant (_root_.SerrePositivity.SimplicialModel.RelativeChoiceSpace.obj i b) :=
    (isFibrant_iff_of_isTerminal (_root_.SerrePositivity.SimplicialModel.RelativeChoiceSpace.projection i b) SSet.stdSimplex.isTerminalObj₀).mpr
      ⟨(projection_trivialFibration hcof hfib i b p hp).1⟩
  apply (SSet.modelCategoryQuillen.fibration_iff (terminal.from (_root_.SerrePositivity.SimplicialModel.RelativeChoiceSpace.obj i b))).mpr
  rw [← hfib]
  exact mem_fibrations _

include hcof hfib in
lemma extension {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p) {K L : SSet.{v}} (j : K ⟶ L) [Mono j]
    (a : K ⟶ _root_.SerrePositivity.SimplicialModel.RelativeChoiceSpace.obj i b) : ∃ e : L ⟶ _root_.SerrePositivity.SimplicialModel.RelativeChoiceSpace.obj i b, j ≫ e = a := by
  have hj : cofibrations SSet.{v} j := by rw [hcof]; infer_instance
  have : HasLiftingProperty j (_root_.SerrePositivity.SimplicialModel.RelativeChoiceSpace.projection i b) := MorphismProperty.hasLiftingProperty_of_wfs _ _
    hj (projection_trivialFibration hcof hfib i b p hp)
  let sq : CommSq a j (_root_.SerrePositivity.SimplicialModel.RelativeChoiceSpace.projection i b) (SSet.stdSimplex.isTerminalObj₀.from L) :=
    ⟨SSet.stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

include hcof hfib in
lemma interval {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p)
    (s t : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ _root_.SerrePositivity.SimplicialModel.RelativeChoiceSpace.obj i b) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ _root_.SerrePositivity.SimplicialModel.RelativeChoiceSpace.obj i b,
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
        T ◁ _root_.SerrePositivity.SimplicialModel.RelativeChoiceSpace.pointUnitIso.hom ≫ (ρ_ T).hom ≫ e₀ ∧
      T ◁ SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫ H =
        T ◁ _root_.SerrePositivity.SimplicialModel.RelativeChoiceSpace.pointUnitIso.hom ≫ (ρ_ T).hom ≫ e₁ ∧
      i ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ≫ H =
        V ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫ _root_.SerrePositivity.SimplicialModel.RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ V).hom ≫ b := by
  obtain ⟨e, hs, ht⟩ := interval hcof hfib i b p hp (_root_.SerrePositivity.SimplicialModel.RelativeChoiceSpace.ofExtension i b e₀ h₀) (_root_.SerrePositivity.SimplicialModel.RelativeChoiceSpace.ofExtension i b e₁ h₁)
  refine ⟨_root_.SerrePositivity.SimplicialModel.RelativeChoiceSpace.family i b e, ?_, ?_, _root_.SerrePositivity.SimplicialModel.RelativeChoiceSpace.family_fixed_boundary i b e⟩
  · rw [← _root_.SerrePositivity.SimplicialModel.RelativeChoiceSpace.family_naturality, hs, _root_.SerrePositivity.SimplicialModel.RelativeChoiceSpace.family_ofExtension]
  · rw [← _root_.SerrePositivity.SimplicialModel.RelativeChoiceSpace.family_naturality, ht, _root_.SerrePositivity.SimplicialModel.RelativeChoiceSpace.family_ofExtension]

include hcof hfib in
lemma nonempty_fixedBoundaryHomotopy {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p) (e₀ e₁ : T ⟶ P) (h₀ : i ≫ e₀ = b) (h₁ : i ≫ e₁ = b) :
    Nonempty (_root_.SerrePositivity.SimplicialModel.RelativeChoiceSpace.FixedBoundaryHomotopy i b e₀ e₁) := by
  obtain ⟨H, h₀, h₁, hb⟩ := relative_homotopy hcof hfib i b p hp e₀ e₁ h₀ h₁
  exact ⟨⟨H, h₀, h₁, hb⟩⟩

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison
