module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.StrictDiagramMappingSpace

/-!
概要：strict な変換の同じ成分評価の自然性を、内部 Hom の射の等式へ束ねる。
方針：元の各単体の自然性を全次数・全パラメーターで使う。
規約：図式の値の充填性を要求しない。
使われ方：一次元セルの同じ変換空間の pullback 正方形。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 内部 Hom の前合成は、元の任意の次数の関手単体を同じ射で評価する。 -/
lemma internalHomPre_evaluate {A B X : SSet.{u}} (i : A ⟶ B)
    {n k : SimplexCategoryᵒᵖ} (θ : ((ihom B).obj X).obj n) (α : n ⟶ k) (x : A.obj k) :
    (((pre i).app X).app n θ).app k α x = θ.app k α (i.app k x) := by
  have h := MonoidalClosed.uncurry_pre_app X
    (𝟙 ((ihom B).obj X) : (ihom B).obj X ⟶ (ihom B).obj X) i
  rw [Category.id_comp] at h
  have hk := congrArg (fun f ↦ f.app k (x, ((ihom B).obj X).map α θ)) h
  have hn := ((pre i).app X).naturality_apply α θ
  change (((pre i).app X).app k (((ihom B).obj X).map α θ)).app k (𝟙 k) x =
    θ.app k (α ≫ 𝟙 k) (i.app k x) at hk
  rw [hn] at hk
  change (((pre i).app X).app n θ).app k (α ≫ 𝟙 k) x =
    θ.app k (α ≫ 𝟙 k) (i.app k x) at hk
  simpa only [Category.comp_id] using hk

/-- 同じ strict 変換の成分の自然性は、全内部 Hom の元の射の等式。 -/
lemma strictDiagramMappingComponent_naturality
    {C : Type u} [Category.{u} C] (F G : C ⥤ SSet.{u}) {c d : C} (f : c ⟶ d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F G c ≫ (ihom (F.obj c)).map (G.map f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F G d ≫ (pre (F.map f)).app (G.obj d) := by
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_pre_app]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, η⟩
  exact η.property f n (𝟙 n) x

/-- 有限二点順序の元の唯一の非恒等射。 -/
def strictIntervalIndexArrow : (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) ⟶ ULift.up 1 :=
  homOfLE (by decide)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
