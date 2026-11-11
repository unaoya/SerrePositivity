module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SkeletalCellGluing
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SigmaHomotopyGluing
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpanHomotopyGluing

/-! # 下骨格とセル比較の全時刻の貼り合わせ

概要：下骨格と各新セル上の実ホモトピーから、次骨格の同じ二端点の実ホモトピーを作る。
方針：セル族を余積へ貼り、区間との積が保存する骨格 pushout で接着する。
規約：下骨格・全セル上の制限を厳密に保つ。使われ方：有限係数相対充填の一段。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory SSet SSet.relativeCellComplexOfMono
open CartesianMonoidalCategory
open scoped _root_.Simplicial
variable {L K Y : SSet.{u}} (i : L ⟶ K) (n : ℕ)
/-- セル境界の定値ホモトピーは下骨格の定値ホモトピーの制限と一致する。 -/
lemma skeletalCellBoundary_constant (c : Cell i n) (g : K ⟶ Y) :
    fst (∂Δ[n] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (∂Δ[n]).ι ≫ c.map ≫ g =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalCellBoundary i n c ▷ (Δ[1] : SSet.{u})) ≫
        fst _ _ ≫ (skeletonOfMono i n).ι ≫ g := by
  symm
  calc
    _ = fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalCellBoundary i n c ≫ (skeletonOfMono i n).ι ≫ g := by
      rw [← Category.assoc, whiskerRight_fst]
      simp only [Category.assoc]
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun z => fst (∂Δ[n] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ z ≫ g)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalCellBoundary_ι i n c)

variable {f g : (skeletonOfMono i (n + 1) : SSet.{u}) ⟶ Y}
variable (H₀ : SSet.Homotopy (r i n ≫ f) (r i n ≫ g))
variable (Hc : ∀ c : Cell i n, SSet.Homotopy
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalCellInclusion i n c ≫ f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalCellInclusion i n c ≫ g))

/-- 各セル上の実ホモトピーを、全セルの余積の上へ貼る。 -/
def skeletalCellHomotopySigma : SSet.Homotopy (b i n ≫ f) (b i n ≫ g) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sigmaHomotopyGlue (fun _ : Cell i n => (Δ[n] : SSet.{u}))
    (fun c => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (Hc c) (Category.assoc _ _ _) (Category.assoc _ _ _))

/-- 余積上へ貼ったホモトピーは各指定セルの全時刻を保つ。 -/
lemma skeletalCellHomotopySigma_cell (c : Cell i n) :
    (c.ιSigmaStdSimplex ▷ (Δ[1] : SSet.{u})) ≫ (skeletalCellHomotopySigma i n Hc).h =
      (Hc c).h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sigmaHomotopyGlue_ι _ _ c

variable (hw : ∀ c : Cell i n, ((∂Δ[n]).ι ▷ (Δ[1] : SSet.{u})) ≫ (Hc c).h =
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalCellBoundary i n c ▷ (Δ[1] : SSet.{u})) ≫ H₀.h)

include hw

/-- 各セル境界の一致は pushout 全体の接着条件を与える。 -/
lemma skeletalHomotopyGlue_compatible :
    (t i n ▷ (Δ[1] : SSet.{u})) ≫ H₀.h =
      (l i n ▷ (Δ[1] : SSet.{u})) ≫ (skeletalCellHomotopySigma i n Hc).h := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sigmaTensor_hom_ext (fun _ : Cell i n => (∂Δ[n] : SSet.{u}))
  intro c
  rw [← Category.assoc, ← comp_whiskerRight]
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalCellBoundary i n c ▷ Δ[1]) ≫ H₀.h =
    (c.ιSigmaBoundary ▷ Δ[1]) ≫ (l i n ▷ Δ[1]) ≫ (skeletalCellHomotopySigma i n Hc).h
  rw [← Category.assoc, ← comp_whiskerRight, Cell.ι_l, comp_whiskerRight, Category.assoc,
    skeletalCellHomotopySigma_cell]
  exact (hw c).symm

/-- 下骨格と各セルの比較を、次骨格上の一つの実ホモトピーへ貼り合わせる。 -/
def skeletalHomotopyGlue : SSet.Homotopy f g :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pushoutHomotopy (isPushout i n) H₀ (skeletalCellHomotopySigma i n Hc)
    (skeletalHomotopyGlue_compatible i n H₀ Hc hw)

/-- 貼り合わせ後も下骨格の全時刻は指定どおり。 -/
lemma skeletalHomotopyGlue_previous :
    (r i n ▷ (Δ[1] : SSet.{u})) ≫ (skeletalHomotopyGlue i n H₀ Hc hw).h = H₀.h :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pushoutHomotopy_inl _ _ _ _

/-- 貼り合わせ後も各セルの全時刻は指定どおり。 -/
lemma skeletalHomotopyGlue_cell (c : Cell i n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalCellInclusion i n c ▷ (Δ[1] : SSet.{u})) ≫
      (skeletalHomotopyGlue i n H₀ Hc hw).h = (Hc c).h := by
  change ((c.ιSigmaStdSimplex ≫ b i n) ▷ Δ[1]) ≫ _ = _
  rw [comp_whiskerRight, Category.assoc]
  unfold skeletalHomotopyGlue
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pushoutHomotopy_inr]
  exact skeletalCellHomotopySigma_cell i n Hc c

end SerrePositivity.InfinityCategories.Project.DerivedCategories
