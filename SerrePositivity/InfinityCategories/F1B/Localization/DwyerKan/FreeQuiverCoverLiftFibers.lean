module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FreeQuiverCoverGroupoid
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.GroupoidPostcomposeEquiv

/-!
# 元の被覆の自由 groupoid の始点を固定した射のファイバー

概要：基底頂点・持ち上げ頂点のラベル・同じ持ち上げ射を記録する。
方針：元の二重従属和へ同じ射を入れ、各固定終点での単射性を回収する。
規約：元の持ち上げ射を商の別表示へ置き換えない。
使われ方：自由 groupoid 間の射影の忠実性の置換表現。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

def LiftFiber :
    letI := quiver A
    Quiver.FreeGroupoid (Vertex A) → Q → Type (max u v) := by
  letI := quiver A
  intro S B
  exact Σ β : (Quiver.FreeGroupoid.of Q).obj A ⟶ (Quiver.FreeGroupoid.of Q).obj B,
    S ⟶ (Quiver.FreeGroupoid.of (Vertex A)).obj (⟨B, β⟩ : Vertex A)

def LiftStar : letI := quiver A; Quiver.FreeGroupoid (Vertex A) → Type (max u v) := by
  letI := quiver A
  intro S
  exact Σ B, LiftFiber A S B

def encodeStar :
    letI := quiver A
    ∀ (S x : Quiver.FreeGroupoid (Vertex A)), (S ⟶ x) → LiftStar A S := by
  letI := quiver A
  intro S x h
  exact ⟨x.as.base, x.as.path, h⟩

lemma encodeStar_injective :
    letI := quiver A
    ∀ S x : Quiver.FreeGroupoid (Vertex A), Function.Injective (encodeStar A S x) := by
  let := quiver A
  intro S x h k he
  have he' := eq_of_heq (Sigma.mk.inj_iff.mp he).2
  exact eq_of_heq (Sigma.mk.inj_iff.mp he').2

def liftFiberEquiv :
    letI := quiver A
    ∀ (S : Quiver.FreeGroupoid (Vertex A)) {B E : Q} (_ : B ⟶ E),
      LiftFiber A S B ≃ LiftFiber A S E := by
  letI := quiver A
  intro S B E f
  exact Equiv.sigmaCongr
    (groupoidPostcomposeEquiv ((Quiver.FreeGroupoid.of Q).obj A) ((Quiver.FreeGroupoid.of Q).map f))
    (fun β => groupoidPostcomposeEquiv S
      ((Quiver.FreeGroupoid.of (Vertex A)).map (forwardArrow A (⟨B, β⟩ : Vertex A) f)))

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
