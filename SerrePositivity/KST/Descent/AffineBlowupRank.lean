module

public import SerrePositivity.KST.Descent.AffineFlatRefinement
public import SerrePositivity.KST.Descent.FiniteFlatRankCover

/-!
# アフィン平坦化後の blowup の既約性と正の定 rank

## 概要
整なアフィン基底の平坦化で得た非零境界から blowup の既約性を証明し、rank を一定にする。

## 方針
中心外同型と境界の稠密性で既約な稠密開部分を得て、rank の局所定数性を使う。

## 規約
blowup の既約性や大域的な定 rank を追加の仮定にしない。被約性は結論しない。

## 使われ方
論文 補題 3.3 の平坦化後の被覆から補題 3.2 の有理 transfer の正規化へ接続する。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open SerrePositivity.KST.SchemeLemmas

namespace SerrePositivity.KST.Descent

set_option backward.isDefEq.respectTransparency false in
/-- 概要：非零境界を避ける中心の実際の blowup は既約（論文 補題 3.3）。
方針：中心外同型で既約な開部分を得て、その稠密性を境界の稠密性から導く。
規約：元の基底の整性とアフィン性を明示し、blowup の既約性は証明する。
使われ方：平坦化後の有限忠実平坦被覆の rank の一様性。 -/
theorem blowup_irreducible_of_affine_boundary {Y : Scheme.{u}} [IsAffine Y] [IsIntegral Y]
    (J : Y.IdealSheafData) (r : Γ(Y, ⊤)) (hr : r ≠ 0)
    (hadm : Y.basicOpen r ≤ _root_.SerrePositivity.AlgebraicGeometry.centerComplement J) : IrreducibleSpace (_root_.SerrePositivity.AlgebraicGeometry.blowup J) := by
  let U := _root_.SerrePositivity.AlgebraicGeometry.centerComplement J
  let V := _root_.SerrePositivity.AlgebraicGeometry.blowupπ J ⁻¹ᵁ U
  obtain ⟨y, hy⟩ := affine_basicOpen_nonempty_of_ne_zero Y r hr
  have : Nonempty U := ⟨⟨y, hadm hy⟩⟩
  have : IrreducibleSpace U := U.ι.isOpenEmbedding.irreducibleSpace
  have : IsIso (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J ∣_ U) := _root_.SerrePositivity.AlgebraicGeometry.blowupπ_restrict_complement_isIso J
  have : IrreducibleSpace V := (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J ∣_ U).homeomorph.irreducibleSpace_iff.mpr
    (inferInstance : IrreducibleSpace U)
  have hd : Dense V.carrier :=
    (blowup_boundary_dense_of_isAffine J r
      (mem_nonZeroDivisors_iff_ne_zero.mpr hr)).mono (fun _ hx ↦ hadm hx)
  have hi := (IrreducibleSpace.isIrreducible_univ V).image V.ι V.ι.continuous.continuousOn
  simp only [Set.image_univ, Scheme.Opens.range_ι] at hi
  apply (irreducibleSpace_def (_root_.SerrePositivity.AlgebraicGeometry.blowup J)).mpr
  exact Eq.mp (congrArg IsIrreducible hd.closure_eq) hi.closure

/-- 概要：既約基底上の有限忠実平坦有限表示射は正の定 rank（論文 補題 3.2）。
方針：非空な基底の一点を選び、局所定数関数の連結空間上の一様性と全射性を使う。
規約：rank の値を仮定せず、実際の射から取り出す。
使われ方：平坦化後の同じ被覆の transfer を一つの正整数で正規化する。 -/
theorem exists_positive_constant_finrank {X Y : Scheme.{u}} [IrreducibleSpace Y]
    (p : X ⟶ Y) [IsFinite p] [Flat p] [Surjective p] [LocallyOfFinitePresentation p] :
    ∃ d : ℕ, 0 < d ∧ ∀ y : Y, p.finrank y = d := by
  let y₀ : Y := Classical.choice (inferInstance : Nonempty Y)
  refine ⟨p.finrank y₀, ?_, ?_⟩
  · exact Nat.lt_of_lt_of_le Nat.zero_lt_one
      ((p.one_le_finrank_iff_surjective.mpr inferInstance) y₀)
  · intro y
    exact p.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace y y₀

/-- 概要：アフィン平坦化の実際の被覆に正の定 rank と低次元の中心を同時に供給（補題 3.3）。
方針：構成済みの中心・細分に blowup の既約性を適用し、中心の真閉性で次元を下げる。
規約：有限上界 d を明示する。定 rank も中心上の次元低下も独立した入力にしない。
使われ方：補題 3.2 の有理 transfer と補題 3.3 の中心上の次元帰納の共通の幾何入力。 -/
theorem exists_affine_flat_refinement_with_rank_and_dimension
    {S : Scheme.{u}} [IsNoetherian S] {X Y : FiniteTypeSchemes S}
    (f : X ⟶ Y) [IsFinite f.hom.left] [Surjective f.hom.left]
    [IsAffine Y.obj.left] [IsIntegral Y.obj.left]
    (d : ℕ) (bound : topologicalKrullDim Y.obj.left ≤ d) :
    ∃ J : Y.obj.left.IdealSheafData, J.support ≠ ⊤ ∧
      topologicalKrullDim (finiteTypeBlowupSquare Y J).square.X₃.obj.left < d ∧
      ∃ (T : FiniteTypeSchemes S) (p : T ⟶ finiteTypeBlowup Y J)
        (a : T ⟶ finiteTypePullback f (finiteTypeBlowupProjection Y J)) (rank : ℕ),
        IsFinite p.hom.left ∧ Flat p.hom.left ∧ Surjective p.hom.left ∧
        LocallyOfFinitePresentation p.hom.left ∧ 0 < rank ∧
        (∀ y, p.hom.left.finrank y = rank) ∧
        a ≫ finiteTypePullbackSnd f (finiteTypeBlowupProjection Y J) = p := by
  obtain ⟨r, J, hr, _, hadm, hproper, T, p, a, hpfin, hpflat, hpsurj, hpfp, ha⟩ :=
    exists_affine_finiteFlat_refinement f
  have : IsFinite p.hom.left := hpfin
  have : Flat p.hom.left := hpflat
  have : Surjective p.hom.left := hpsurj
  have : LocallyOfFinitePresentation p.hom.left := hpfp
  have : IrreducibleSpace (finiteTypeBlowup Y J).obj.left :=
    blowup_irreducible_of_affine_boundary J r hr hadm
  obtain ⟨rank, hpos, hrank⟩ := exists_positive_constant_finrank p.hom.left
  have hproperSet : (J.support : Set Y.obj.left) ≠ Set.univ := by
    intro h
    apply hproper
    exact SetLike.coe_injective h
  have hdim : topologicalKrullDim (finiteTypeBlowupSquare Y J).square.X₃.obj.left < d :=
    reducedClosedSubscheme_dimension_lt_bound J.support hproperSet d bound
  exact ⟨J, hproper, hdim, T, p, a, rank, hpfin, hpflat, hpsurj, hpfp, hpos, hrank, ha⟩

end SerrePositivity.KST.Descent
