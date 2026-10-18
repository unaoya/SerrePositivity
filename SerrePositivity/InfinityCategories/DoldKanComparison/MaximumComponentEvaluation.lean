module

public import SerrePositivity.InfinityCategories.DoldKanComparison.MaximumFlagImage

/-!
# 終点付き頂点集合の最大頂点による成分評価

概要：終点付き集合の内部立方体の評価は、元の標準単体の対応する成分に次数符号を掛ける。
方針：全旗の評価式と昇順の旗の像の同定を合わせ、単射な引き戻しの成分を計算する。
規約：次数は指定した k と濃度の証明で取り、表示の差を HEq で吸収する。
使われ方：HA 1.3.1.17、Kerodon 2.5.9 の二つの比較射の合成が恒等となる式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DoldKanComparison
open CategoryTheory DifferentialGraded
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] {x y : D}

/-- 概要：選んだ非空集合の終点付き立方体の評価は元の成分の次数符号倍である。
方針：唯一の昇順の旗が元の頂点集合を通るので、その単射な引き戻しの最上位成分を取る。
規約：J が一点の場合も含み、追加の閉性や充填の仮定はない。
使われ方：Kerodon 2.5.9 の実際の比較射と逆向きの射の成分の一致。 -/
lemma cubeEvaluation_withLast_maximum {n : ℕ} (σ : StandardSimplex R x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    HEq (cubeEvaluation
      (descendingEnumeration (coherentVertexInterior.{u} (DGNerve.PinchedHom.withLast J)
        (J.min' hJ).castSucc (Fin.last (n + 1))))
      (pathCubeMap (show (ULift.up (J.min' hJ).castSucc : ULift.{u} (Fin (n + 2))) <
        ULift.up (Fin.last (n + 1)) from Fin.castSucc_lt_last _) _ ≫
          pathLastMaximumMap (J.min' hJ) ≫ SSet.yonedaEquiv.symm σ))
      (degreeSign (J.card - 1) • σ.val.component J k hJ hk) := by
  let S := coherentVertexInterior.{u} (DGNerve.PinchedHom.withLast J)
    (J.min' hJ).castSucc (Fin.last (n + 1))
  let e := descendingEnumeration S
  let e' := Fin.revPerm.trans e
  have hAsc : StrictMono e' := (descendingEnumeration_strictAnti S).comp Fin.rev_strictAnti
  let α := maximumFlagOrder (J.min' hJ) S e'
  have hα : Function.Injective α := (maximumFlagOrder_strictMono _ _ _ hAsc).injective
  have hImage : Finset.univ.image α = J :=
    (maximumFlagOrder_image _ _ _ hAsc).trans (withLast_interior_source_image J hJ)
  have hc : S.card + 1 = J.card := by
    have h := Finset.card_image_of_injective Finset.univ hα
    rw [hImage] at h
    simpa using h.symm
  have hdeg : k = -(S.card : ℤ) := by omega
  subst hdeg
  apply heq_of_eq
  change cubeEvaluation e _ = _
  rw [cubeEvaluation_maximum _ _ e (descendingEnumeration_strictAnti S) σ,
    standardTopEval_pullback_injective _ _ hα]
  have hsign : degreeSign S.card = degreeSign (J.card - 1) := congrArg degreeSign (by omega)
  rw [hsign]
  apply congrArg (fun z ↦ degreeSign (J.card - 1) • z)
  exact eq_of_heq (component_heq_of_eq σ.val _ J hImage _ _ _ hJ _ hk)

end SerrePositivity.InfinityCategories.DoldKanComparison
