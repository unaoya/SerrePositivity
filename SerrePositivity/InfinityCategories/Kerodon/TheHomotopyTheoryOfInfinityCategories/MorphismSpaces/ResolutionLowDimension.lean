module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionHomotopyReduction

/-!
# 零・一次元の標準単体の解像は厳密に標準単体である

概要：頂点が高々二つなら旗の各集合は始点と最大元の間の閉区間であり、射影は同型となる。
方針：閉区間内の点は左右いずれかの端点なので、区間による切断が両側の逆になる。
規約：解像の値域の次数 n に n ≤ 1 を課し、旗の次数には制限しない。
使われ方：HA 1.3.1.17、Kerodon Proposition 4.6.7.23（Tag 01LW） の解像の比較の低次の基底。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open CategoryTheory
open scoped _root_.Simplicial

/-- 概要：頂点が高々二つの旗の各集合は始点から最大元までの閉区間である。
方針：任意の区間内の点が二端点のいずれかに等しいことを有限順序で示す。
規約：旗の単体次数 d は任意。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の低次の射影の厳密な逆性。 -/
lemma resolutionFlag_sets_eq_interval_of_le_one {n d : ℕ} (hn : n ≤ 1)
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) (t : Fin (d + 1)) :
    F.sets t = Finset.Icc F.start (F.maxAt t) := by
  apply Finset.ext
  intro j
  constructor
  · intro hj
    exact Finset.mem_Icc.mpr ⟨F.lower t j hj, F.le_maxAt t j hj⟩
  · intro hj
    obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hj
    have he : j = F.start ∨ j = F.maxAt t := by
      by_cases h : j = F.start
      · exact Or.inl h
      · right
        apply Fin.ext
        have hj := j.isLt
        have hs := F.start.isLt
        have hm := (F.maxAt t).isLt
        have hne : j.val ≠ F.start.val := fun he ↦ h (Fin.ext he)
        change F.start.val ≤ j.val at hl
        change j.val ≤ (F.maxAt t).val at hr
        omega
    rcases he with rfl | rfl
    · exact F.start_mem t
    · exact F.maxAt_mem t

/-- 概要：低次の解像では射影の後に区間の切断を取っても恒等になる。
方針：始点は零段の最大元で回収し、各集合は閉区間の式で回収する。
規約：既存の逆向きの恒等式と合わせて同型を与える。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の低次の基底の恒等式。 -/
lemma resolutionProjection_section_of_le_one {n : ℕ} (hn : n ≤ 1) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection.{u} n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSection n = 𝟙 _ := by
  apply CategoryTheory.NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro F
  apply ULift.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.ext
  · exact F.down.maxAt_zero
  · funext t
    change Finset.Icc (F.down.maxAt 0) (F.down.maxAt t) = F.down.sets t
    rw [F.down.maxAt_zero]
    exact (resolutionFlag_sets_eq_interval_of_le_one hn F.down t).symm

/-- 概要：零・一次元の標準単体への解像の射影は厳密な同型である。
方針：逆射に区間の切断を使い、両方向の恒等式を適用する。
規約：一般次数の射影のホモトピー同値性より強い低次の主張。
使われ方：HA 1.3.1.17 の比較射の低次の完全な回収。 -/
def resolutionProjectionIsoOfLeOne {n : ℕ} (hn : n ≤ 1) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n ≅ (Δ[n] : SSet.{u}) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSection n
  hom_inv_id := resolutionProjection_section_of_le_one hn
  inv_hom_id := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSection_projection n

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
