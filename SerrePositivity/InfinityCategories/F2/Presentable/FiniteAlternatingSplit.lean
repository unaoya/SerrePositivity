module

public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteStageSourceCoslice
public import SerrePositivity.InfinityCategories.F2.Presentable.SimplexTerminalFaceAnodyne
public import SerrePositivity.InfinityCategories.F2.Presentable.RelativeSplitCompStruct

/-!
概要：全交互前置図式を保持し、元の後続表示段への分裂三角形を構成する。
方針：偶数前置図式の下で compact 因子化し、right anodyne な偶数面から全前置図式へ持ち上げる。
規約：元の増大余錐を恒等長辺とし、後続段の全余錐と元の表示脚を厳密に保持する。
使われ方：fiber の可算交互図式の再帰的な有限段階。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：全前置図式を固定した次の分裂三角形は、元の後続表示段と全表示脚に整合する。
方針：有限前置図式の compact 切断と全二単体の正規化持ち上げを合成する。
規約：整合は coslice 内の実頂点・実辺であり、元の全 join 図式を含む。
使われ方：元の対象上の全交互図式の有限段階の延長。 -/
lemma exists_finiteAlternating_split
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {I : SSet.{u}} [Quasicategory I] [IsKappaFiltered μ I]
    {B : SSet.{u + 1}} [Quasicategory B] {n : ℕ}
    (a : (Δ[n] : SSet.{u}) ⟶ I)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B)
    (c : JoinCocone D) (hc : IsColimitCone c)
    (ha : Compact.IsKappaCompact.{u, u + 1} μ
      ((finiteStageBaseMap a ≫ D).app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last n))))
    (hv : Compact.IsKappaCompact.{u, u + 1} μ c.vertex)
    (F : (Δ[2 * n] : SSet.{u + 1}) ⟶ B)
    (cF : (sliceUnder F) _⦋0⦌)
    (heven : SSet.stdSimplex.map (sequentialEvenFace n) ≫ F = finiteStageBaseMap a ≫ D)
    (haug : joinMap (SSet.stdSimplex.map (sequentialEvenFace n)) (𝟙 Δ[0]) ≫ cF.val =
      (c.restrict (finiteStageBaseMap a)).val) :
    let s := (finiteStageSourceCosliceIso a).hom
    let G := s ≫ sliceUnderPostcomp (finiteStageBaseMap a) D
    let V := sourceCosliceRestrictedCocone (finiteStageBaseMap a) s D c
    let Q := normalizedCoconeRestriction F (SSet.stdSimplex.map (sequentialEvenFace n)) heven
    ∃ (j : (sliceUnder a) _⦋0⦌) (d : (sliceUnder F) _⦋0⦌)
      (e : (sliceUnder F).Edge cF d) (r : (sliceUnder F).Edge d cF)
      (_T : e.CompStruct r (SSet.Edge.id cF)),
      Q.app (Opposite.op ⦋0⦌) d = G.app (Opposite.op ⦋0⦌) (ULift.up j) ∧
      Q.app (Opposite.op ⦋1⦌) r.edge = (Compact.coconeTransportLeg V (ULift.up j)).edge := by
  let s := (finiteStageSourceCosliceIso a).hom
  let V := sourceCosliceRestrictedCocone (finiteStageBaseMap a) s D c
  let Q := normalizedCoconeRestriction F (SSet.stdSimplex.map (sequentialEvenFace n)) heven
  obtain ⟨j, t, ⟨T⟩⟩ := finiteStage_compact_presentation_section hμ a D c hc ha hv
  have hbase : joinMap (SSet.stdSimplex.map (sequentialEvenFace n)) (𝟙 Δ[0]) ≫ cF.val =
      V.vertex.val := by
    dsimp only [V]
    rw [sourceCosliceRestrictedCocone_vertex]
    exact haug
  obtain ⟨d, e, r, S, hS⟩ := exists_normalizedCoslice_splitCompStruct
    (SSet.stdSimplex.map (sequentialEvenFace n)) (sequentialEvenFace_rightAnodyne n)
    F (finiteStageBaseMap a ≫ D) heven cF V.vertex hbase T.simplex T.d₁
  refine ⟨j, d, e, r, S, ?_, ?_⟩
  · exact compStruct_middle_image_of_simplex_eq Q S T hS
  · have h := congrArg (fun z ↦ (sliceUnder (finiteStageBaseMap a ≫ D)).δ 0 z) hS
    rw [← SSet.δ_naturality_apply, S.d₀, T.d₀] at h
    exact h

end SerrePositivity.InfinityCategories.F2.Presentable
