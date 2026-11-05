module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Core.StdSimplexProductMap
public import SerrePositivity.InfinityCategories.F1B.Adjunction.ConstantFunctor
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering

/-!
概要：矢印を終点の恒等矢印へ縮める、全単体に自然な区間族。
方針：区間の二変数の max を元の矢印で評価する。
規約：終点評価と定値矢印上では厳密に時間に定値。使われ方：終点評価の実随伴。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.ArrowTarget
end SerrePositivity.KST.LocalizingInvariants.ArrowTarget
namespace SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget
open SerrePositivity.KST.LocalizingInvariants.ArrowTarget

def intervalMax : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] := stdSimplexProductMap {
  toFun p := max p.1 p.2
  monotone' _ _ h := max_le_max h.1 h.2 }

lemma intervalMax_zero : lift (𝟙 (Δ[1] : SSet.{u}))
    (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫ intervalMax = 𝟙 Δ[1] := by
  apply stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  fin_cases i <;> rfl

lemma intervalMax_one : lift (𝟙 (Δ[1] : SSet.{u}))
    (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ intervalMax =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  apply stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  fin_cases i <;> rfl

lemma intervalMax_left_one : lift
    (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫ intervalMax =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  apply stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  fin_cases i <;> rfl

variable (X : SSet.{u})
abbrev arrows := (ihom (Δ[1] : SSet.{u})).obj X

def target : arrows X ⟶ X := evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
def identityArrow : X ⟶ arrows X := constantFunctorMap Δ[1] X

def contraction : arrows X ⊗ (Δ[1] : SSet.{u}) ⟶ arrows X :=
  curry (lift (lift (fst Δ[1] (arrows X ⊗ Δ[1]))
      (snd Δ[1] (arrows X ⊗ Δ[1]) ≫ snd (arrows X) Δ[1]) ≫ intervalMax)
    (snd Δ[1] (arrows X ⊗ Δ[1]) ≫ fst (arrows X) Δ[1]) ≫ (ihom.ev Δ[1]).app X)

lemma identityArrow_target : identityArrow X ≫ target X = 𝟙 X := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  change X.map (𝟙 n) x = x
  exact CategoryTheory.Functor.map_id_apply X n x

lemma contraction_zero : SSet.ι₀ ≫ contraction X = 𝟙 (arrows X) := by
  apply uncurry_injective
  rw [uncurry_natural_left, contraction, uncurry_curry, uncurry_id_eq_ev]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨i, f⟩
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app intervalMax_zero (Opposite.op ⦋n⦌)) i
  change intervalMax.app _ (i, PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n) = i at h
  change f.app (Opposite.op ⦋n⦌) (𝟙 _) (intervalMax.app _
    (i, PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n)) = f.app _ (𝟙 _) i
  rw [h]

lemma contraction_one : SSet.ι₁ ≫ contraction X = target X ≫ identityArrow X := by
  apply uncurry_injective
  rw [uncurry_natural_left, contraction, uncurry_curry, uncurry_natural_left]
  change _ = (Δ[1] ◁ target X) ≫ uncurry (constantFunctorMap Δ[1] X)
  rw [constantFunctorMap, uncurry_curry]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨i, f⟩
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app intervalMax_one (Opposite.op ⦋n⦌)) i
  change intervalMax.app _ (i, PinchedHom.constant (stdSimplex.obj₀Equiv.symm 1) n) =
    PinchedHom.constant (stdSimplex.obj₀Equiv.symm 1) n at h
  change f.app (Opposite.op ⦋n⦌) (𝟙 _) (intervalMax.app _
    (i, PinchedHom.constant (stdSimplex.obj₀Equiv.symm 1) n)) =
      f.app _ (𝟙 _) (PinchedHom.constant (stdSimplex.obj₀Equiv.symm 1) n)
  rw [h]

end SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.arrows (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ArrowTarget.arrows := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.arrows

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.contraction (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ArrowTarget.contraction := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.contraction

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ArrowTarget.contraction_one := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.contraction_one

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ArrowTarget.contraction_zero := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.contraction_zero

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.identityArrow (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ArrowTarget.identityArrow := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.identityArrow

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ArrowTarget.identityArrow_target := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.identityArrow_target

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.intervalMax (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ArrowTarget.intervalMax := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.intervalMax

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ArrowTarget.intervalMax_left_one := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.intervalMax_left_one

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ArrowTarget.intervalMax_one := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.intervalMax_one

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ArrowTarget.intervalMax_zero := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.intervalMax_zero

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.target (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ArrowTarget.target := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.target

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ArrowTarget.contraction.eq_1 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.contraction.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ArrowTarget.intervalMax._proof_1 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.intervalMax._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.ArrowTarget.target._proof_1 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.target._proof_1
