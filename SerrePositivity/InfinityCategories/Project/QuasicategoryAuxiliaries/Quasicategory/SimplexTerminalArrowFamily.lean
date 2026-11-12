module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.StdSimplexProductMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathIso

/-!
概要：有限線型図式から最後の頂点への同じ全辺族を構成する。
方針：標準単体の恒等から終頂点への単調な変形を使う。
規約：最後の頂点では恒等辺を厳密に保ち、図式の頂点ごとの選択はしない。
使われ方：c5 の図式の終端を分母に沿って置換する全 cospan 族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- 恒等から終頂点へ動かし、終頂点自身は固定する単調な変形。 -/
def simplexTerminalContractionOrder (n : ℕ) : Fin (n + 1) × Fin 2 →o Fin (n + 1) where
  toFun p := if p.2 = 0 then p.1 else Fin.last n
  monotone' := by
    intro p q hpq
    by_cases hq : q.2 = 0
    · have hp : p.2 = 0 := le_antisymm (hq ▸ hpq.2) (Fin.zero_le _)
      simpa only [hp, hq, ite_true] using hpq.1
    · simp only [hq, ite_false]
      exact Fin.le_last _

/-- 元の有限線型図式の恒等から最後の頂点への指定された変形。 -/
def simplexTerminalContraction (n : ℕ) :
    SSet.Homotopy (𝟙 (Δ[n] : SSet.{u}))
      (SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last n))) where
  h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalContractionOrder n)
  h₀ := by
    apply SSet.hom_ext
    rintro ⟨⟨m⟩⟩
    apply ConcreteCategory.hom_ext
    intro a
    apply stdSimplex.ext
    intro j
    rfl
  h₁ := by
    apply SSet.hom_ext
    rintro ⟨⟨m⟩⟩
    apply ConcreteCategory.hom_ext
    intro a
    apply stdSimplex.ext
    intro j
    rfl
  rel := by
    apply SSet.hom_ext
    intro m
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 元の全図式の各頂点から同じ最後の頂点へ向かう全単体上の辺族。 -/
def simplexTerminalArrowFamily {X : SSet.{u}} {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ X) :
    (Δ[n] : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  curry ((β_ (Δ[1] : SSet.{u}) Δ[n]).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalContraction n).h ≫ D)

/-- 辺族の始点は元の同じ全図式。 -/
lemma simplexTerminalArrowFamily_source {X : SSet.{u}} {n : ℕ}
    (D : (Δ[n] : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalArrowFamily D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      D := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalArrowFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval]
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[n] : SSet.{u}) ≫ (β_ Δ[1] Δ[n]).hom =
      (SSet.ι₀ : (Δ[n] : SSet.{u}) ⟶ Δ[n] ⊗ Δ[1]) := rfl
  rw [← Category.assoc, ← Category.assoc, hp, (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalContraction n).h₀,
    Category.id_comp]

/-- 辺族の終点は元の最後の頂点に厳密に定値。 -/
lemma simplexTerminalArrowFamily_target {X : SSet.{u}} {n : ℕ}
    (D : (Δ[n] : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalArrowFamily D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      SSet.const (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalArrowFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval]
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[n] : SSet.{u}) ≫ (β_ Δ[1] Δ[n]).hom =
      (SSet.ι₁ : (Δ[n] : SSet.{u}) ⟶ Δ[n] ⊗ Δ[1]) := rfl
  rw [← Category.assoc, ← Category.assoc, hp, (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalContraction n).h₁,
    SSet.const_comp]

/-- 最後の頂点での辺は、同じ元の値の恒等辺に厳密に一致する。 -/
lemma simplexTerminalArrowFamily_last {X : SSet.{u}} {n : ℕ}
    (D : (Δ[n] : SSet.{u}) ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalArrowFamily D).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) :
          (Δ[1] : SSet.{u}) ⟶ X) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro m α
  have hα : α = (SimplexCategory.const m.unop ⦋0⦌ 0).op := Subsingleton.elim _ _
  subst α
  obtain ⟨⟨m⟩⟩ := m
  apply ConcreteCategory.hom_ext
  intro t
  trans D.app (Opposite.op ⦋m⦌) ((Δ[n] : SSet.{u}).map
    (SimplexCategory.const ⦋m⦌ ⦋0⦌ 0).op
    (stdSimplex.obj₀Equiv.symm (Fin.last n)))
  · apply congrArg (D.app (Opposite.op ⦋m⦌))
    apply stdSimplex.ext
    intro j
    change (if t j = 0 then Fin.last n else Fin.last n) = Fin.last n
    split_ifs <;> rfl
  · exact ConcreteCategory.congr_hom
      (D.naturality (SimplexCategory.const ⦋m⦌ ⦋0⦌ 0).op)
      (stdSimplex.obj₀Equiv.symm (Fin.last n))

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalArrowFamily (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexTerminalArrowFamily := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalArrowFamily

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexTerminalArrowFamily_last := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalArrowFamily_last

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexTerminalArrowFamily_source := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalArrowFamily_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexTerminalArrowFamily_target := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalArrowFamily_target

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalContraction (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexTerminalContraction := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalContraction

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalContractionOrder (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexTerminalContractionOrder := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalContractionOrder

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexTerminalArrowFamily.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalArrowFamily.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexTerminalContraction._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalContraction._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexTerminalContraction._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalContraction._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexTerminalContraction._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalContraction._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexTerminalContractionOrder._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalContractionOrder._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexTerminalContractionOrder._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalContractionOrder._proof_2
