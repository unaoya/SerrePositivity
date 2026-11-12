module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullHom

/-!
概要：元の実零化面の二つの二単体を、同じ固定 ν のまま取り出す。
方針：四辺と三頂点を回収し、元の二単体の端点 Hom を照合する。
規約：三角形を別の合成代表に置き換えない。
使われ方：実面の同じ高次データを保つ相対充填。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 概要：同じ実零化面の始点は元の核入力の頂点。
方針：元の包含辺の始点を回収する。
規約：元の実 S 面を保つ。使われ方：端点 Hom の始域照合。 -/
lemma dgOdotMilnorPerfectNullSquare_source_vertex :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgOdotMilnorPerfectNullSquare R d) 0 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotMilnorFlatKernelInput R d) := by
  have hs := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_source (dgOdotMilnorPerfectNullSquare R d)
  let e : (dgKInputInfinity.{u, u + 1} R).Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotMilnorFlatKernelInput R d))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotMilnorCellInput R d)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorFlatKernelInputMap R d)
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgOdotMilnorPerfectNullSquare R d =
      SSet.yonedaEquiv.symm e.edge := (dgOdotMilnorPerfectNullSquare_edges R d).1
  rw [hb, Equiv.apply_symm_apply, e.src_eq] at hs
  exact hs.symm

/-- 概要：同じ実零化面の終点は元の resolved 商入力の頂点。
方針：元の実商辺の終点を回収する。
規約：完備化後の別入力へ置換しない。使われ方：端点 Hom の終域照合。 -/
lemma dgOdotMilnorPerfectNullSquare_target_vertex :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgOdotMilnorPerfectNullSquare R d) 1 1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotMilnorResolvedInput R d) := by
  have hs := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target (dgOdotMilnorPerfectNullSquare R d)
  let e : (dgKInputInfinity.{u, u + 1} R).Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotMilnorCellInput R d))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotMilnorResolvedInput R d)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorCellProjectionInputMap R d)
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorPerfectNullSquare R d =
      SSet.yonedaEquiv.symm e.edge := (dgOdotMilnorPerfectNullSquare_edges R d).2.1
  rw [hr, Equiv.apply_symm_apply, e.tgt_eq] at hs
  exact hs.symm

/-- 概要：元の実零化面に含まれる同じ二つの固定 ν 二単体。
方針：正方形の標準二三角形で制限し、同じ ν で写す。
規約：新しい二単体を選ばない。使われ方：実面比較の端点 Hom データ。 -/
def dgOdotMilnorNuNullTriangle (j : Fin 2) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} _⦋2⦌ :=
  SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle j ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)

/-- 概要：両二単体の始点は同じ元核の固定 ν 値。
方針：三角形の最初の頂点と実面の始点を照合する。
規約：同じ二単体の対象写像の等号。使われ方：豊穣 Hom の始域輸送。 -/
lemma dgOdotMilnorNuNullTriangle_source (j : Fin 2) :
    (dgOdotMilnorNuNullTriangle R d j).obj ⟨ULift.up (0 : Fin 3)⟩ =
      dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d) := by
  let F := dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R
  let t := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u + 2} j)
  have hn := NatTrans.naturality_apply F
    (SimplexCategory.const ⦋0⦌ ⦋2⦌ (0 : Fin 3)).op t
  have hs : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}).map
      (SimplexCategory.const ⦋0⦌ ⦋2⦌ (0 : Fin 3)).op t =
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2),
          stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    fin_cases j <;> apply Prod.ext <;> apply SSet.stdSimplex.ext <;>
      intro i <;> fin_cases i <;> rfl
  have he : (dgOdotMilnorNuNullTriangle R d j).obj ⟨ULift.up (0 : Fin 3)⟩ =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0) := by
    have hn' := congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject hn
    rw [hs] at hn'
    exact hn'.symm
  rw [he]
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject ((dgKInputNu R).app _
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgOdotMilnorPerfectNullSquare R d) 0 0)) = _
  rw [dgOdotMilnorPerfectNullSquare_source_vertex, dgKInputNu_vertex, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex]

/-- 概要：両二単体の終点は同じ元 resolved 商の固定 ν 値。
方針：三角形の最後の頂点と実面の終点を照合する。
規約：同じ二単体の対象写像の等号。使われ方：豊穣 Hom の終域輸送。 -/
lemma dgOdotMilnorNuNullTriangle_target (j : Fin 2) :
    (dgOdotMilnorNuNullTriangle R d j).obj ⟨ULift.up (2 : Fin 3)⟩ =
      dgKInputStableValue R (dgOdotMilnorResolvedInput R d) := by
  let F := dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R
  let t := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u + 2} j)
  have hn := NatTrans.naturality_apply F
    (SimplexCategory.const ⦋0⦌ ⦋2⦌ (2 : Fin 3)).op t
  have hs : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}).map
      (SimplexCategory.const ⦋0⦌ ⦋2⦌ (2 : Fin 3)).op t =
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2),
          stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
    fin_cases j <;> apply Prod.ext <;> apply SSet.stdSimplex.ext <;>
      intro i <;> fin_cases i <;> rfl
  have he : (dgOdotMilnorNuNullTriangle R d j).obj ⟨ULift.up (2 : Fin 3)⟩ =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 1) := by
    have hn' := congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject hn
    rw [hs] at hn'
    exact hn'.symm
  rw [he]
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject ((dgKInputNu R).app _
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgOdotMilnorPerfectNullSquare R d) 1 1)) = _
  rw [dgOdotMilnorPerfectNullSquare_target_vertex, dgKInputNu_vertex, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex]

/-- 概要：零角経由の元二単体の中間対象は同じ実全対象商の零安定圏。
方針：元の二単体の中間頂点を実面の零角へ自然性で戻す。
規約：零圏を選び直さない。使われ方：元二単体の全 Hom の零性。 -/
lemma dgOdotMilnorNuNullTriangle_middle_zero :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory ((dgOdotMilnorNuNullTriangle R d 0).obj ⟨ULift.up (1 : Fin 3)⟩) := by
  let F := dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R
  let t := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u + 2} 0)
  have hn := NatTrans.naturality_apply F
    (SimplexCategory.const ⦋0⦌ ⦋2⦌ (1 : Fin 3)).op t
  have hs : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}).map
      (SimplexCategory.const ⦋0⦌ ⦋2⦌ (1 : Fin 3)).op t =
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2),
          stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
    apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl
  have he : (dgOdotMilnorNuNullTriangle R d 0).obj ⟨ULift.up (1 : Fin 3)⟩ =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 1) := by
    have hn' := congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject hn
    rw [hs] at hn'
    exact hn'.symm
  rw [he]
  exact dgOdotMilnorPerfectNullSquare_zero R d

/-- 概要：元の実二単体の全 Hom データを同じ核と resolved 商の Hom で読む。
方針：元の豊穣関手の Hom 作用を、証明済みの端点等号で輸送する。
規約：元の二単体の Hom 写像を変更しない。使われ方：零合成空間への因子分解。 -/
def dgOdotMilnorNuNullTriangleHom (j : Fin 2) :
    nerve (CategoryTheory.SimplicialThickening.Path
      (ULift.up.{u + 1} (0 : Fin 3)) (ULift.up.{u + 1} (2 : Fin 3))) ⟶
        SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1})
          (dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d))
          (dgKInputStableValue R (dgOdotMilnorResolvedInput R d)) :=
  (dgOdotMilnorNuNullTriangle R d j).map ⟨ULift.up (0 : Fin 3)⟩
    ⟨ULift.up (2 : Fin 3)⟩ ≫
      eqToHom (congrArg₂ (fun X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1} => SimplicialCategory.sHom X Y)
        (dgOdotMilnorNuNullTriangle_source R d j) (dgOdotMilnorNuNullTriangle_target R d j))

end SerrePositivity.KST.SConstruction
