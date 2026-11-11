module
public import SerrePositivity.KST.SConstruction.TerminalSuffixFamily
public import SerrePositivity.KST.SConstruction.PointedPullbackFiber

/-! # 終点固定 path の fiber 内の収縮ホモトピー
概要：元の区間族を動かし、その境界像の suffix と共に homotopy fiber へ持ち上げる。
方針：suffix の始点が元の境界像に等しいことを pullback の普遍性へ渡す。
規約：零時刻の path から一時刻の定数 path へ進む向きを保つ。使われ方：元の零行の Ω 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 元の射の終点固定 path による homotopy fiber。 -/
def terminalPathHomotopyFiber {E B : PointedSimplicialSet.{u}} (f : E ⟶ B) :
    PointedSimplicialSet.{u} := pullback (terminalPathStart B) f

/-- 区間族の一時刻の境界が基点なら、その零時刻と path の族を fiber へ持ち上げる。 -/
def terminalPathFamilyFiberMap {A : SSet.{u}} {E B : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ E.right)
    (h₁ : SSet.ι₁ ≫ h ≫ f.right = toUnit A ≫ B.hom) :
    A ⟶ (terminalPathHomotopyFiber f).right :=
  (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_isPullback (terminalPathStart B) f).lift
    (terminalPathFamily B (h ≫ f.right) h₁) (SSet.ι₀ ≫ h)
    ((terminalPathFamily_start B (h ≫ f.right) h₁).trans (Category.assoc _ _ _).symm)

/-- 厳密な零合成を定数 path と共に終点固定 fiber へ持ち上げる。 -/
def terminalStrictZeroFiberMap {A : SSet.{u}} {E B : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (a : A ⟶ E.right) (ha : a ≫ f.right = toUnit A ≫ B.hom) :
    A ⟶ (terminalPathHomotopyFiber f).right :=
  (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_isPullback (terminalPathStart B) f).lift
    (toUnit A ≫ (terminalPathSpace B).hom) a (by
      rw [Category.assoc, Under.w]
      exact ha.symm)

/-- 元の区間族とその境界の suffix を fiber 内で同時に動かす cylinder。 -/
def terminalFiberCylinder {A : SSet.{u}} {E B : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ E.right)
    (h₁ : SSet.ι₁ ≫ h ≫ f.right = toUnit A ≫ B.hom) :
    A ⊗ (Δ[1] : SSet.{u}) ⟶ (terminalPathHomotopyFiber f).right :=
  (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_isPullback (terminalPathStart B) f).lift
    (terminalSuffixFamily B (h ≫ f.right) h₁) h
    (terminalSuffixFamily_start B (h ≫ f.right) h₁)

/-- fiber 内の cylinder は時刻零で元の区間族の path を回収する。 -/
lemma terminalFiberCylinder_zero {A : SSet.{u}} {E B : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ E.right) (h₁) :
    SSet.ι₀ ≫ terminalFiberCylinder f h h₁ = terminalPathFamilyFiberMap f h h₁ := by
  apply (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_isPullback (terminalPathStart B) f).hom_ext
  · simp only [terminalFiberCylinder, terminalPathFamilyFiberMap, Category.assoc,
      IsPullback.lift_fst, terminalSuffixFamily_zero]
  · simp only [terminalFiberCylinder, terminalPathFamilyFiberMap, Category.assoc,
      IsPullback.lift_snd]

/-- fiber 内の cylinder は時刻一で定数 path と元の終点の組を回収する。 -/
lemma terminalFiberCylinder_one {A : SSet.{u}} {E B : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ E.right) (h₁) :
    SSet.ι₁ ≫ terminalFiberCylinder f h h₁ =
      terminalStrictZeroFiberMap f (SSet.ι₁ ≫ h) ((Category.assoc _ _ _).trans h₁) := by
  apply (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_isPullback (terminalPathStart B) f).hom_ext
  · simp only [terminalFiberCylinder, terminalStrictZeroFiberMap, Category.assoc,
      IsPullback.lift_fst, terminalSuffixFamily_one]
  · simp only [terminalFiberCylinder, terminalStrictZeroFiberMap, Category.assoc,
      IsPullback.lift_snd]

/-- 元の向きの区間族から fiber 内の二つの具体的比較の実ホモトピーを得る。 -/
def terminalFiberHomotopy {A : SSet.{u}} {E B : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ E.right) (h₁) :
    SSet.Homotopy (terminalPathFamilyFiberMap f h h₁)
      (terminalStrictZeroFiberMap f (SSet.ι₁ ≫ h) ((Category.assoc _ _ _).trans h₁)) where
  h := terminalFiberCylinder f h h₁
  h₀ := terminalFiberCylinder_zero f h h₁
  h₁ := terminalFiberCylinder_one f h h₁
  rel := by ext n ⟨⟨x, hx⟩, t⟩; exact hx.elim

end SerrePositivity.KST.SConstruction
