module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SkeletalExtension
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite

/-! # 相対骨格のセル単体の厳密な貼り合わせ

概要：下骨格と各セルの充填から次の骨格への写像を作り、両方への制限を保持する。
方針：標準相対セル pushout の desc を使う。
規約：有限単体集合では各次数のセル族が有限。使われ方：閉係数充填の一段更新。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits SSet SSet.relativeCellComplexOfMono
open scoped _root_.Simplicial
variable {L K X : SSet.{u}} (i : L ⟶ K) (n : ℕ)

/-- 各相対セルの下骨格への指定境界写像。 -/
def skeletalCellBoundary (c : Cell i n) : (∂Δ[n] : SSet.{u}) ⟶ skeletonOfMono i n :=
  c.ιSigmaBoundary ≫ t i n

/-- 各相対セルの次骨格への指定単体写像。 -/
def skeletalCellInclusion (c : Cell i n) : (Δ[n] : SSet.{u}) ⟶ skeletonOfMono i (n + 1) :=
  c.ιSigmaStdSimplex ≫ b i n

/-- セル境界は元の単体の境界として同じ K に含まれる。 -/
lemma skeletalCellBoundary_ι (c : Cell i n) :
    skeletalCellBoundary i n c ≫ (skeletonOfMono i n).ι = (∂Δ[n]).ι ≫ c.map := by
  change (c.ιSigmaBoundary ≫ t i n) ≫ _ = _
  rw [Category.assoc, c.ι_t_ι_eq_ι_l_b_ι, c.ι_b_ι]

/-- セル境界の次骨格への像は指定した単体の同じ境界。 -/
lemma skeletalCellBoundary_next (c : Cell i n) :
    skeletalCellBoundary i n c ≫ r i n = (∂Δ[n]).ι ≫ skeletalCellInclusion i n c := by
  change (c.ιSigmaBoundary ≫ t i n) ≫ r i n = _
  rw [Category.assoc, w, ← Category.assoc, Cell.ι_l, Category.assoc]
  rfl

/-- 有限な K では、任意の相対骨格の同じ次数のセル族は有限。 -/
lemma finiteSkeletalCells [K.Finite] : Finite (Cell i n) :=
  Finite.of_injective (fun c : Cell i n => (⟨c.simplex, c.nonDegenerate⟩ : K.nonDegenerate n))
    (fun _ _ h => Cell.ext (congrArg Subtype.val h))

variable (f : (skeletonOfMono i n : SSet.{u}) ⟶ X)
variable (U : Cell i n → ((Δ[n] : SSet.{u}) ⟶ X))
variable (hU : ∀ c, (∂Δ[n]).ι ≫ U c = skeletalCellBoundary i n c ≫ f)

include hU

/-- 個々のセルの境界一致を余積の接着条件に束ねる。 -/
lemma skeletalCellGlue_compatible : t i n ≫ f = l i n ≫ Sigma.desc U := by
  apply Sigma.hom_ext
  intro c
  change (c.ιSigmaBoundary ≫ t i n) ≫ f = (c.ιSigmaBoundary ≫ l i n) ≫ Sigma.desc U
  rw [Cell.ι_l]
  simpa only [Category.assoc, Sigma.ι_comp_desc, skeletalCellBoundary] using (hU c).symm

/-- 指定された全セル単体を持つ、次骨格への実写像。 -/
def skeletalCellGlue : (skeletonOfMono i (n + 1) : SSet.{u}) ⟶ X :=
  (isPushout i n).desc f (Sigma.desc U) (skeletalCellGlue_compatible i n f U hU)

/-- 下骨格への制限は元の同じ写像。 -/
lemma skeletalCellGlue_previous : r i n ≫ skeletalCellGlue i n f U hU = f :=
  (isPushout i n).inl_desc _ _ _

/-- 各セルへの制限も指定された同じ実単体。 -/
lemma skeletalCellGlue_cell (c : Cell i n) :
    skeletalCellInclusion i n c ≫ skeletalCellGlue i n f U hU = U c := by
  change (c.ιSigmaStdSimplex ≫ b i n) ≫ _ = _
  unfold skeletalCellGlue
  rw [Category.assoc, (isPushout i n).inr_desc, Sigma.ι_comp_desc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
