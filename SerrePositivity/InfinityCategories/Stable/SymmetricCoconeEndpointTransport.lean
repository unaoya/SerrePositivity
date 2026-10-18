module
public import SerrePositivity.InfinityCategories.Stable.CoconeTransportChange
public import SerrePositivity.InfinityCategories.Stable.CoconeEndpointGluing
public import SerrePositivity.InfinityCategories.Stable.SymmetricCoconeKernelPairSwap

/-! # 対称 span の二枝と可換な終点輸送

概要：共通始点で選んだ余錐の終点輸送を枝へ持ち上げ、対称 span 全体の輸送を両枝と可換に構成する。
方針：同じ枝の二つの図式表示へ戻した区間族が共通始点で一致することを示して貼り合わせる。
規約：先に選んだ共通始点の輸送を変更しない。使われ方：全体の輸送の自己引き戻し表示との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：共通始点の終点輸送を固定し、同じ枝と対称 span 全体の終点輸送を同時に選べる。
方針：枝の輸送を制限に沿って持ち上げ、その二つの表示の共通始点での一致を使って全体へ貼る。
規約：X の quasicategory 性のみ。枝の終点の零性や全体の余極限性は不要。
使われ方：自己引き戻しと全体の余錐空間の終点輸送の照合。 -/
lemma exists_symmetricCoconeEndpointTransport {X : SSet.{u}} [Quasicategory X]
    {x z : X _⦋0⦌} (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z)
    {y₀ y₁ : X _⦋0⦌} (a : SSet.Truncated.Edge (X := (truncation 2).obj X) y₀ y₁)
    (S : LeftFibrationFiberTransport
      (sliceUnderProjection (stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm f.edge)) a) :
    ∃ (T : LeftFibrationFiberTransport (sliceUnderProjection (SSet.yonedaEquiv.symm f.edge)) a)
      (U : LeftFibrationFiberTransport (sliceUnderProjection (edgeSpan f f)) a),
      T.h ≫ sliceUnderRestrict (SSet.yonedaEquiv.symm f.edge) (stdSimplex.δ (1 : Fin 2)) =
        (coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y₀ ▷ (Δ[1] : SSet.{u})) ≫ S.h ∧
      T.map ≫ coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y₁ =
        coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y₀ ≫ S.map ∧
      U.map ≫ symmetricCoconeFirst f y₁ = symmetricCoconeFirst f y₀ ≫ T.map ∧
      U.map ≫ symmetricCoconeSecond f y₁ = symmetricCoconeSecond f y₀ ≫ T.map := by
  obtain ⟨T, hT, hmT⟩ := exists_coconeEndpointTransport_restrict
    (SSet.yonedaEquiv.symm f.edge) (stdSimplex.δ (1 : Fin 2)) a S
  let Tb := T.changeDiagram (edgeSpan_left f f).symm
  let Tc := T.changeDiagram (edgeSpan_right f f).symm
  let W := coconeMappingSpace (edgeSpan f f) y₀
  have Hb := T.changeDiagram_uncurry (edgeSpan_left f f).symm
    (cosliceRestrictionFiberMap (edgeSpan f f) horn₂₀.ι₀₁ y₀)
  have Hc := T.changeDiagram_uncurry (edgeSpan_right f f).symm
    (cosliceRestrictionFiberMap (edgeSpan f f) horn₂₀.ι₀₂ y₀)
  have Hb' : joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 (W ⊗ (Δ[1] : SSet.{u}))) ≫
      sliceUnderUncurry ((cosliceRestrictionFiberMap (edgeSpan f f) horn₂₀.ι₀₁ y₀ ▷ Δ[1]) ≫ Tb.h) =
    joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 (W ⊗ (Δ[1] : SSet.{u}))) ≫
      sliceUnderUncurry ((symmetricCoconeFirst f y₀ ▷ Δ[1]) ≫ T.h) :=
    congrArg (fun v => joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 (W ⊗ (Δ[1] : SSet.{u}))) ≫ v) Hb
  have Hc' : joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 (W ⊗ (Δ[1] : SSet.{u}))) ≫
      sliceUnderUncurry ((cosliceRestrictionFiberMap (edgeSpan f f) horn₂₀.ι₀₂ y₀ ▷ Δ[1]) ≫ Tc.h) =
    joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 (W ⊗ (Δ[1] : SSet.{u}))) ≫
      sliceUnderUncurry ((symmetricCoconeSecond f y₀ ▷ Δ[1]) ≫ T.h) :=
    congrArg (fun v => joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 (W ⊗ (Δ[1] : SSet.{u}))) ≫ v) Hc
  have H₁ := coconeEndpointTransport_restrict_uncurry (SSet.yonedaEquiv.symm f.edge)
    (stdSimplex.δ (1 : Fin 2)) a T S hT (symmetricCoconeFirst f y₀)
  have H₂ := coconeEndpointTransport_restrict_uncurry (SSet.yonedaEquiv.symm f.edge)
    (stdSimplex.δ (1 : Fin 2)) a T S hT (symmetricCoconeSecond f y₀)
  have H₀ := congrArg (fun v => sliceUnderUncurry ((v ▷ (Δ[1] : SSet.{u})) ≫ S.h))
    (symmetricCoconeBranches_comm f y₀)
  have hglue := Hb'.trans (H₁.trans (H₀.trans (H₂.symm.trans Hc'.symm)))
  obtain ⟨U, _, _, hmB, hmC⟩ := exists_coconeEndpointTransport_glue horn₂₀.isPushout
    (edgeSpan f f) a Tb Tc hglue
  refine ⟨T, U, hT, hmT, ?_, ?_⟩
  · change U.map ≫ (cosliceRestrictionFiberMap _ horn₂₀.ι₀₁ y₁ ≫ _) =
      (cosliceRestrictionFiberMap _ horn₂₀.ι₀₁ y₀ ≫ _) ≫ T.map
    rw [← Category.assoc, hmB, Category.assoc,
      T.changeDiagram_map (edgeSpan_left f f).symm, ← Category.assoc]
  · change U.map ≫ (cosliceRestrictionFiberMap _ horn₂₀.ι₀₂ y₁ ≫ _) =
      (cosliceRestrictionFiberMap _ horn₂₀.ι₀₂ y₀ ≫ _) ≫ T.map
    rw [← Category.assoc, hmC, Category.assoc,
      T.changeDiagram_map (edgeSpan_right f f).symm, ← Category.assoc]

end SerrePositivity.InfinityCategories
