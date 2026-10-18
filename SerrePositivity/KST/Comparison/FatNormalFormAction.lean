module

public import SerrePositivity.KST.Comparison.FatNormalFormEquiv

/-!
# fat realization の標準形への単体作用

概要：各次数の標準形に単体作用を適用した後の正規化と、その次元の減少を計算する。
方針：各行からの包含の自然性と、標準単体の作用の合成を使う。
規約：Segal 1974 Proposition 1.6、Appendix A の有限骨格の計算。
使われ方：標準形の次元で定義する骨格が部分単体集合であること。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial

/--
概要：全射な標準形から戻した元への単体作用は、同じ行の作用と全射の前合成で表せる。
方針：各行の包含の自然性を元で評価する。
規約：作用の後で全射であるとは限らない。
使われ方：作用後の像分解への帰着。
-/
theorem fatNormalFormRealize_action (F : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    {d e : SimplexCategoryᵒᵖ} (θ : d ⟶ e) (p : FatNormalForm F d) :
    (fatRealization F).map θ (fatNormalFormRealize F d p) =
      (fatRealizationInclusion F p.degree.len).app e
        ((F.obj (op p.degree)).map θ p.simplex,
          SSet.stdSimplex.objEquiv.symm (θ.unop ≫ p.epi)) := by
  have h := congrArg (fun t => t
    ((p.simplex, SSet.stdSimplex.objEquiv.symm p.epi) :
      (F.obj (op p.degree) ⊗ SSet.stdSimplex.obj p.degree).obj d))
        ((fatRealizationInclusion F p.degree.len).naturality θ)
  change (fatRealizationInclusion F p.degree.len).app e
    ((F.obj (op p.degree)).map θ p.simplex,
      (SSet.stdSimplex.obj p.degree).map θ (SSet.stdSimplex.objEquiv.symm p.epi)) =
        (fatRealization F).map θ (fatNormalFormRealize F d p) at h
  rw [SSet.stdSimplex.map_objEquiv_symm] at h
  exact h.symm

/--
概要：単体作用の後の正規化は、元の全射に作用の射を前合成して正規化したものである。
方針：標準形からの復元、包含での正規化の計算則を順に使う。
規約：行の元には内側の単体作用を使う。
使われ方：正規化の次元の不等式。
-/
theorem fatDegreeNormalize_action (F : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    {d e : SimplexCategoryᵒᵖ} (θ : d ⟶ e) (y : (fatRealization F).obj d) :
    fatDegreeNormalize F e ((fatRealization F).map θ y) =
      fatNormalize F e
        ((F.obj (op (fatDegreeNormalize F d y).degree)).map θ (fatDegreeNormalize F d y).simplex)
        (θ.unop ≫ (fatDegreeNormalize F d y).epi) := by
  have h := fatNormalFormRealize_action F θ (fatDegreeNormalize F d y)
  rw [fatNormalFormRealize_degreeNormalize] at h
  rw [h, fatDegreeNormalize_inclusion, Equiv.apply_symm_apply]

/--
概要：単体作用で標準形の終域の次元は増えない。
方針：合成の像の包含が単射なので、像の次元は元の終域以下である。
規約：作用の向きは反変の単体圏の射。
使われ方：fat realization の有限骨格の部分単体集合の条件。
-/
theorem fatNormalDegree_action_le (F : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    {d e : SimplexCategoryᵒᵖ} (θ : d ⟶ e) (y : (fatRealization F).obj d) :
    (fatDegreeNormalize F e ((fatRealization F).map θ y)).degree.len ≤
      (fatDegreeNormalize F d y).degree.len := by
  rw [fatDegreeNormalize_action]
  exact SimplexCategory.len_le_of_mono
    (image.ι (θ.unop ≫ (fatDegreeNormalize F d y).epi))

/--
概要：標準形の終域の次元は、その単体の次数以下である。
方針：標準形に記録された全射は単体の次元を下げる。
規約：全射性を仮定せず、正規化の構成から得る。
使われ方：各次数で有限骨格が全体になること。
-/
theorem fatNormalDegree_le (F : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) (y : (fatRealization F).obj d) :
    (fatDegreeNormalize F d y).degree.len ≤ d.unop.len := by
  let p := fatDegreeNormalize F d y
  let : Epi p.epi := p.epi_property
  exact SimplexCategory.len_le_of_epi p.epi

end SerrePositivity.KST.Comparison
