module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FiltrationCoordinates
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeBasisFiltration

/-! # Semifree filtration と高さ付き基底の同値

概要：既存の semifree 定義と自然数値を持つ semibasis の存在は同値である。
方針：filtration の初期段と商の直和基底に段番号を割り当てる。
規約：元の定義を変更しない。使われ方：任意の射の cone の基底構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable {S : Type u} [CommRing S] {M : ModuleCategory S PUnit.{1}}
namespace SemifreeFiltration

/-- 概要：既存の semifree filtration から高さ付き基底を構成する。
方針：各商の基底に段番号を付け、微分の商座標の消滅を使う。
規約：初期基底の高さは零。使われ方：既存 semifree 性から semibasis を取り出す。 -/
def toBasis (F : ModuleSemifreeFiltration S PUnit.{1} M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis S ((moduleEvaluation S PUnit.{1} PUnit.unit).obj M) where
  Index k := Σ n, letI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeFiltration.piece_free F k n;
    Module.Free.ChooseBasisIndex S ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeFiltration.splitSequence F k).piece n)
  basis := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeFiltration.basis F
  height _ a := a.1
  lowering k a b hb := by
    classical
    by_contra hn
    have hle : a.1 ≤ b.1 := Nat.le_of_not_gt hn
    have hz : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeFiltration.basis F (k + 1)).repr
        (((moduleEvaluation S PUnit.{1} PUnit.unit).obj M).d k (k + 1)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeFiltration.basis F k a)) b = 0 := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeFiltration.basis_repr, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeFiltration.basis_apply]
      rcases a with ⟨n, a⟩
      cases n with
      | zero =>
        rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeFiltration.degreeLinearEquiv_symm_lof_zero, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeFiltration.stageLeg_zero_d]
        simp only [map_zero, DFinsupp.zero_apply, Finsupp.zero_apply]
      | succ n =>
        rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeFiltration.degreeLinearEquiv_symm_lof_succ]
        have hj : n < b.1 := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hle
        have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeFiltration.section_d_coordinates F k n b.1 hj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeFiltration.pieceBasis F k (n + 1) a)
        rw [h, map_zero, Finsupp.zero_apply]
    exact (Finsupp.mem_support_iff.mp hb) hz

end SemifreeFiltration

/-- 概要：既存定義で semifree な複体には高さ付き基底が存在する。
方針：一点加群の filtration を取り出し、その基底を評価する。
規約：有界性や有限性の前提なし。使われ方：cone の基底構成への入力。 -/
theorem complexSemifree_nonempty_basis {P : Complex S} (hP : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S P) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis S P) := by
  obtain ⟨F⟩ := hP
  exact ⟨SemifreeFiltration.toBasis F⟩

/-- 概要：既存の semifree 条件は高さ付き基底の存在と同値である。
方針：filtration からの基底構成と基底からの filtration 構成を組み合わせる。
規約：元の `complexSemifree` の定義を使う。使われ方：基底による閉性の証明。 -/
theorem complexSemifree_iff_nonempty_basis (P : Complex S) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S P ↔ Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis S P) :=
  ⟨complexSemifree_nonempty_basis, fun ⟨B⟩ => B.complexSemifree⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
