module

public import SerrePositivity.KST.Comparison.OverFinitePresentable
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.CategoryTheory.LiftingProperties.Over
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable

/-!
# 基底上の horn 生成射

概要：基底上の horn に小対象構成を適用する。
方針：有限表示性と、台の horn の持ち上げ条件との同値を証明する。
規約：Waldhausen LNM 1126 §1.7・§1.8 の局所係数比較の補助構成。
使われ方：局所係数ホモロジー同型の anodyne map への拡張。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

/--
概要：基底への単体の射から基底上の horn 包含を作る。
方針：構造射を horn 包含との合成にする。
規約：次元は正の n + 1。
使われ方：slice の生成射。
-/
def overHornMap {B : SSet.{u}} (n : ℕ) (k : Fin (n + 2))
    (τ : (Δ[n + 1] : SSet.{u}) ⟶ B) :
    Over.mk ((Λ[n + 1, k]).ι ≫ τ) ⟶ Over.mk τ :=
  Over.homMk (Λ[n + 1, k]).ι rfl

/--
概要：基底上の全ての正次元 horn 包含の射の性質。
方針：次元、欠けた面、基底への単体で添字付ける。
規約：添字の宇宙は基底と同じ。
使われ方：小対象構成の生成集合。
-/
def overHornGenerators (B : SSet.{u}) : MorphismProperty (Over B) :=
  ⨆ n, MorphismProperty.ofHoms (fun a : Σ _k : Fin (n + 2),
    ((Δ[n + 1] : SSet.{u}) ⟶ B) => overHornMap n a.1 a.2)

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType

instance (B : SSet.{u}) (n : ℕ) : MorphismProperty.IsSmall.{u}
    (MorphismProperty.ofHoms (fun a : Σ _k : Fin (n + 2),
      ((Δ[n + 1] : SSet.{u}) ⟶ B) => overHornMap n a.1 a.2)) :=
  MorphismProperty.isSmall_ofHoms ..

instance (B : SSet.{u}) : MorphismProperty.IsSmall.{u} (overHornGenerators B) :=
  MorphismProperty.isSmall_iSup ..

instance (B : SSet.{u}) : MorphismProperty.IsCardinalForSmallObjectArgument
    (overHornGenerators B) Cardinal.aleph0.{u} where
  preservesColimit {A C X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      simp only [overHornGenerators, MorphismProperty.iSup_iff] at hi
      obtain ⟨n, ⟨⟨k, τ⟩⟩⟩ := hi
      have : IsFinitelyPresentable.{u} (Λ[n + 1, k]).toSSet := by infer_instance
      exact @over_isFinitelyPresentable_of_left _ _ (by
        change IsFinitelyPresentable.{u} (Λ[n + 1, k]).toSSet
        infer_instance)
    infer_instance

instance (B : SSet.{u}) : (overHornGenerators B).HasSmallObjectArgument.{u} :=
  ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

/--
概要：基底上の horn の右持ち上げ条件は台の horn の条件に等しい。
方針：底辺と基底への構造射の合成で任意の可換正方形を slice に持ち上げる。
規約：基底に Kan 条件を課さない。
使われ方：台が anodyne な射の slice セル表示。
-/
theorem overHornGenerators_rlp_iff {B : SSet.{u}} {src dst : Over B} (p : src ⟶ dst) :
    (overHornGenerators B).rlp p ↔ SSet.modelCategoryQuillen.J.rlp p.left := by
  constructor
  · intro h A C i hi
    simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
    obtain ⟨n, ⟨k⟩⟩ := hi
    refine ⟨fun {t b} sq => ?_⟩
    let τ := b ≫ dst.hom
    let t' : Over.mk ((Λ[n + 1, k]).ι ≫ τ) ⟶ src := Over.homMk t (by
      change t ≫ src.hom = (Λ[n + 1, k]).ι ≫ (b ≫ dst.hom)
      rw [← Over.w p, ← Category.assoc, sq.w, Category.assoc])
    let b' : Over.mk τ ⟶ dst := Over.homMk b rfl
    have sq' : CommSq t' (overHornMap n k τ) p b' :=
      ⟨Over.OverMorphism.ext sq.w⟩
    have : HasLiftingProperty (overHornMap n k τ) p :=
      h (overHornMap n k τ) (by
        simp only [overHornGenerators, MorphismProperty.iSup_iff]
        exact ⟨n, MorphismProperty.ofHoms.mk
          (f := fun a : Σ _k : Fin (n + 2), ((Δ[n + 1] : SSet.{u}) ⟶ B) =>
            overHornMap n a.1 a.2) ⟨k, τ⟩⟩)
    exact ⟨⟨{ l := sq'.lift.left
              fac_left := congrArg (fun f => f.left) sq'.fac_left
              fac_right := congrArg (fun f => f.left) sq'.fac_right }⟩⟩
  · intro h A C i hi
    simp only [overHornGenerators, MorphismProperty.iSup_iff] at hi
    obtain ⟨n, ⟨⟨k, τ⟩⟩⟩ := hi
    have : HasLiftingProperty (Λ[n + 1, k]).ι p.left :=
      h _ (SSet.modelCategoryQuillen.horn_ι_mem_J (n + 1) k)
    change HasLiftingProperty (overHornMap n k τ) p
    have : HasLiftingProperty (overHornMap n k τ).left p.left := by
      change HasLiftingProperty (Λ[n + 1, k]).ι p.left
      infer_instance
    exact HasLiftingProperty.over _ _

/--
概要：台が anodyne な基底上の射は horn の右持ち上げ射に対して左持ち上げを持つ。
方針：台の持ち上げを slice に戻す。
規約：実際の anodyne 射を仮定する。
使われ方：小対象構成による retract 表示。
-/
theorem overHornGenerators_llp_of_anodyne {B : SSet.{u}} {X Y : Over B}
    (f : X ⟶ Y) (hf : SSet.anodyneExtensions f.left) :
    (overHornGenerators B).rlp.llp f := by
  intro A C p hp
  have : HasLiftingProperty f.left p.left :=
    hf _ ((overHornGenerators_rlp_iff p).mp hp)
  exact HasLiftingProperty.over _ _

/--
概要：台が anodyne な基底上の射は horn セルの超限合成の retract である。
方針：実際の小対象構成と証明済みの左持ち上げ条件を組み合わせる。
規約：余積と超限合成の宇宙は単体の値の宇宙。
使われ方：局所係数の horn の計算を任意の anodyne 射へ拡張する。
-/
theorem overHornGenerators_cellPresentation {B : SSet.{u}} {X Y : Over B}
    (f : X ⟶ Y) (hf : SSet.anodyneExtensions f.left) :
    (MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.coproducts.{u} (overHornGenerators B)).pushouts).retracts f := by
  rw [← MorphismProperty.llp_rlp_of_hasSmallObjectArgument]
  exact overHornGenerators_llp_of_anodyne f hf

end SerrePositivity.KST.Comparison
