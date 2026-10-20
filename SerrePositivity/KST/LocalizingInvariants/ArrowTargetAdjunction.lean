module

public import SerrePositivity.KST.LocalizingInvariants.ArrowTargetContraction
public import SerrePositivity.KST.LocalizingInvariants.RetractionHomotopyAdjunction

/-!
概要：矢印圏の元の終点評価は恒等矢印関手の実左随伴。
方針：max による収縮の前後合成を厳密に計算し、h Fun 全体の三角恒等式へ渡す。
規約：始域に安定性を要求しない。使われ方：cofiber 回転を経た Cone の実右随伴。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.ArrowTarget

variable (X : SSet.{u})

lemma contraction_target : contraction X ≫ target X =
    fst (arrows X) (Δ[1] : SSet.{u}) ≫ target X := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨f, t⟩
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app intervalMax_left_one (Opposite.op ⦋n⦌)) t
  change intervalMax.app _ (PinchedHom.constant (stdSimplex.obj₀Equiv.symm 1) n, t) =
    PinchedHom.constant (stdSimplex.obj₀Equiv.symm 1) n at h
  change f.app (Opposite.op ⦋n⦌) (𝟙 _) (intervalMax.app _
    (PinchedHom.constant (stdSimplex.obj₀Equiv.symm 1) n, t)) =
      f.app _ (𝟙 _) (PinchedHom.constant (stdSimplex.obj₀Equiv.symm 1) n)
  rw [h]

lemma identityArrow_contraction : (identityArrow X ▷ (Δ[1] : SSet.{u})) ≫ contraction X =
    fst X (Δ[1] : SSet.{u}) ≫ identityArrow X := by
  apply uncurry_injective
  rw [uncurry_natural_left, contraction, uncurry_curry, uncurry_natural_left]
  change _ = (Δ[1] ◁ fst X (Δ[1] : SSet.{u})) ≫ uncurry (constantFunctorMap Δ[1] X)
  rw [constantFunctorMap, uncurry_curry]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨i, x, t⟩
  change X.map (𝟙 (Opposite.op ⦋n⦌)) x = x
  exact CategoryTheory.Functor.map_id_apply X _ x

def unitHomotopy : SSet.Homotopy (𝟙 (arrows X)) (target X ≫ identityArrow X) where
  h := contraction X
  h₀ := contraction_zero X
  h₁ := contraction_one X
  rel := by ext n ⟨x, y⟩; exact x.property.elim

/-- 元の終点評価と恒等矢印関手の間の実随伴。 -/
def adjunction [Quasicategory X] : QCatAdjunction (target X) (identityArrow X) :=
  adjunctionOfRetractionHomotopy (identityArrow_target X) (unitHomotopy X)
    (contraction_target X) (identityArrow_contraction X)

end SerrePositivity.KST.LocalizingInvariants.ArrowTarget
