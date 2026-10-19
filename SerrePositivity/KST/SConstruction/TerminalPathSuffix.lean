module
public import SerrePositivity.KST.SConstruction.TerminalPathEvaluation
public import SerrePositivity.KST.SConstruction.CofiberUnitPrism

/-! # 終点固定 path の向きを保つ suffix
概要：元の区間族の時刻 t 以降の部分を max(s,t) によって取り出す。
方針：既存の区間の max を使い、始点・終点・時刻の両端を元の射として計算する。
規約：区間を逆向きにする射は使わない。使われ方：零行 loop と定数 path の fiber 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 元のパラメータを保ち、区間の点 s と時刻 t を max(s,t) へ送る。 -/
def terminalSuffixReparametrization (A : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ (A ⊗ (Δ[1] : SSet.{u})) ⟶ A ⊗ (Δ[1] : SSet.{u}) :=
  lift (snd _ _ ≫ fst _ _)
    (lift (fst _ _) (snd _ _ ≫ snd _ _) ≫ intervalMax)

/-- suffix の元の区間の始点は元の時刻とパラメータを回収する。 -/
lemma terminalSuffixReparametrization_start (A : SSet.{u}) :
    (λ_ (A ⊗ (Δ[1] : SSet.{u}))).inv ≫
      Spectra.KanPath.endpoint 0 ▷ (A ⊗ (Δ[1] : SSet.{u})) ≫
        terminalSuffixReparametrization A = 𝟙 _ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  apply Prod.ext
  · rfl
  · apply ULift.ext
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext j
    change max 0 (stdSimplex.asOrderHom z.2 j) = stdSimplex.asOrderHom z.2 j
    exact max_eq_right (Fin.zero_le _)

/-- suffix の元の区間の終点は元の区間族の終点を回収する。 -/
lemma terminalSuffixReparametrization_end (A : SSet.{u}) :
    terminalPointedInterval.hom ▷ (A ⊗ (Δ[1] : SSet.{u})) ≫
      terminalSuffixReparametrization A =
      snd (𝟙_ SSet.{u}) (A ⊗ (Δ[1] : SSet.{u})) ≫
        fst A (Δ[1] : SSet.{u}) ≫ SSet.ι₁ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  apply Prod.ext
  · rfl
  · apply ULift.ext
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext j
    change max 1 (stdSimplex.asOrderHom z.2.2 j) = 1
    exact max_eq_left (Fin.le_last _)

/-- 時刻零の suffix は元の区間全体。 -/
lemma terminalSuffixReparametrization_zero (A : SSet.{u}) :
    (Δ[1] : SSet.{u}) ◁ (SSet.ι₀ : A ⟶ _) ≫ terminalSuffixReparametrization A =
      (β_ (Δ[1] : SSet.{u}) A).hom := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  apply Prod.ext
  · rfl
  · apply ULift.ext
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext j
    change max (stdSimplex.asOrderHom z.1 j) 0 = stdSimplex.asOrderHom z.1 j
    exact max_eq_left (Fin.zero_le _)

/-- 時刻一の suffix は元の区間族の終点だけを取る。 -/
lemma terminalSuffixReparametrization_one (A : SSet.{u}) :
    (Δ[1] : SSet.{u}) ◁ (SSet.ι₁ : A ⟶ _) ≫ terminalSuffixReparametrization A =
      snd (Δ[1] : SSet.{u}) A ≫ SSet.ι₁ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  apply Prod.ext
  · rfl
  · apply ULift.ext
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext j
    change max (stdSimplex.asOrderHom z.1 j) 1 = 1
    exact max_eq_right (Fin.le_last _)

end SerrePositivity.KST.SConstruction
