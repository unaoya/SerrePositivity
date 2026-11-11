module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.MaximumFlagImage

/-!
# 終点付き頂点集合の最大頂点による成分評価

概要：終点付き集合の内部立方体の評価は、元の標準単体の対応する成分に次数符号を掛ける。
方針：全旗の評価式と昇順の旗の像の同定を合わせ、単射な引き戻しの成分を計算する。
規約：次数は指定した k と濃度の証明で取り、表示の差を HEq で吸収する。
使われ方：HA 1.3.1.17、Kerodon 2.5.9（Tag 00SC） の二つの比較射の合成が恒等となる式。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] {x y : D}

/-- 概要：選んだ非空集合の終点付き立方体の評価は元の成分の次数符号倍である。
方針：唯一の昇順の旗が元の頂点集合を通るので、その単射な引き戻しの最上位成分を取る。
規約：J が一点の場合も含み、追加の閉性や充填の仮定はない。
使われ方：Kerodon 2.5.9（Tag 00SC） の実際の比較射と逆向きの射の成分の一致。 -/
lemma cubeEvaluation_withLast_maximum {n : ℕ} (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.descendingEnumeration (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexInterior.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J)
        (J.min' hJ).castSucc (Fin.last (n + 1))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap (show (ULift.up (J.min' hJ).castSucc : ULift.{u} (Fin (n + 2))) <
        ULift.up (Fin.last (n + 1)) from Fin.castSucc_lt_last _) _ ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap (J.min' hJ) ≫ SSet.yonedaEquiv.symm σ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign (J.card - 1) • σ.val.component J k hJ hk) := by
  let S := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexInterior.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J)
    (J.min' hJ).castSucc (Fin.last (n + 1))
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.descendingEnumeration S
  let e' := Fin.revPerm.trans e
  have hAsc : StrictMono e' := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.descendingEnumeration_strictAnti S).comp Fin.rev_strictAnti
  let α := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.maximumFlagOrder (J.min' hJ) S e'
  have hα : Function.Injective α := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.maximumFlagOrder_strictMono _ _ _ hAsc).injective
  have hImage : Finset.univ.image α = J :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.maximumFlagOrder_image _ _ _ hAsc).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.withLast_interior_source_image J hJ)
  have hc : S.card + 1 = J.card := by
    have h := Finset.card_image_of_injective Finset.univ hα
    rw [hImage] at h
    simpa using h.symm
  have hdeg : k = -(S.card : ℤ) := by omega
  subst hdeg
  apply heq_of_eq
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation e _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation_maximum _ _ e (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.descendingEnumeration_strictAnti S) σ,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval_pullback_injective _ _ hα]
  have hsign : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign S.card = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign (J.card - 1) := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign (by omega)
  rw [hsign]
  apply congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign (J.card - 1) • z)
  exact eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.component_heq_of_eq σ.val _ J hImage _ _ _ hJ _ hk)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
