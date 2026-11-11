module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverGroupoid
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GroupoidPostcomposeEquiv

/-!
# 元の被覆の自由 groupoid の始点を固定した射のファイバー

概要：基底頂点・持ち上げ頂点のラベル・同じ持ち上げ射を記録する。
方針：元の二重従属和へ同じ射を入れ、各固定終点での単射性を回収する。
規約：元の持ち上げ射を商の別表示へ置き換えない。
使われ方：自由 groupoid 間の射影の忠実性の置換表現。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

def LiftFiber :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) → Q → Type (max u v) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro S B
  exact Σ β : (Quiver.FreeGroupoid.of Q).obj A ⟶ (Quiver.FreeGroupoid.of Q).obj B,
    S ⟶ (Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj (⟨B, β⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)

def LiftStar : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A; Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) → Type (max u v) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro S
  exact Σ B, LiftFiber A S B

def encodeStar :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ (S x : Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)), (S ⟶ x) → LiftStar A S := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro S x h
  exact ⟨x.as.base, x.as.path, h⟩

lemma encodeStar_injective :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ S x : Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A), Function.Injective (encodeStar A S x) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro S x h k he
  have he' := eq_of_heq (Sigma.mk.inj_iff.mp he).2
  exact eq_of_heq (Sigma.mk.inj_iff.mp he').2

def liftFiberEquiv :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ (S : Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)) {B E : Q} (_ : B ⟶ E),
      LiftFiber A S B ≃ LiftFiber A S E := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro S B E f
  exact Equiv.sigmaCongr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidPostcomposeEquiv ((Quiver.FreeGroupoid.of Q).obj A) ((Quiver.FreeGroupoid.of Q).map f))
    (fun β => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidPostcomposeEquiv S
      ((Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.forwardArrow A (⟨B, β⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) f)))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
