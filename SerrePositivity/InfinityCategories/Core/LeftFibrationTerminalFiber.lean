module

public import SerrePositivity.InfinityCategories.Core.CocartesianCosliceFiber
public import SerrePositivity.InfinityCategories.Core.TerminalTransport

/-!
概要：始対象を持つ left fibration の終対象上の fiber の充填。
方針：境界上の錐を作り、その基底の錐を終対象で埋めて持ち上げる。
規約：モデル構造を使わず join と境界の持ち上げで構成する。
使われ方：Kerodon §5.1.1・§7.1.5 の輸送と相対終対象。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：始対象から任意の図式への錐が存在する。
方針：coslice 射影の trivial Kan fibration 性を空部分複体に適用する。
規約：図式の始域は任意。
使われ方：Kerodon §4.7.3 の始対象の錐。 -/
lemma IsInitialVertex.exists_cosliceLift {A X : SSet.{u}} {x : X _⦋0⦌}
    (hx : IsInitialVertex x) (b : A ⟶ X) :
    ∃ C : A ⟶ sliceUnder (SSet.yonedaEquiv.symm x),
      C ≫ sliceUnderProjection (SSet.yonedaEquiv.symm x) = b := by
  have := (isInitialVertex_iff_trivialKanFibration x).1 hx
  have := TrivialKanFibration.mem (p := sliceUnderProjection (SSet.yonedaEquiv.symm x))
    (⊥ : A.Subcomplex).ι inferInstance
  have sq : CommSq (Subcomplex.isInitialBot.to (sliceUnder (SSet.yonedaEquiv.symm x)))
      (⊥ : A.Subcomplex).ι (sliceUnderProjection (SSet.yonedaEquiv.symm x)) b :=
    ⟨Subcomplex.isInitialBot.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_right⟩

/-- 概要：左に点を join した標準単体の右因子の最後の頂点は全体の最後の頂点。
方針：連結順序写像の右因子の値を計算する。
規約：右因子の次元は零でもよい。
使われ方：Kerodon §4.7.3 の終対象による join の境界の充填。 -/
lemma joinStdSimplexIso_inr_lastVertex (n : ℕ) :
    SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (Fin.last n)) ≫
      joinInr (Δ[0] : SSet.{u}) Δ[n] ≫ (joinStdSimplexIso 0 n).hom =
        SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (Fin.last (0 + n + 1))) := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply stdSimplex.ext
  intro i
  fin_cases i
  apply Fin.ext
  change (Join.concat (p := 1) (q := n + 1) (r := 1) 0 (by omega)
    (Join.stdAugEquiv.{u} 0 0 PUnit.unit)
    (Join.stdAugEquiv.{u} n 1 (stdSimplex.obj₀Equiv.symm (Fin.last n))) (0 : Fin 1)).val = _
  rw [Join.concat_of_ge _ _ _ _ _ (by omega)]
  change 1 + n = 0 + n + 1
  omega

/-- 概要：点と境界の join 上の図式の右端を終対象に定値とすれば錐全体へ延長できる。
方針：右の面を定値射で貼って標準単体の境界とし、最後の頂点の終対象性で埋める。
規約：X の quasicategory 性は不要。
使われ方：Kerodon §7.1.5 の相対終対象の輸送の充填。 -/
lemma IsTerminalVertex.exists_pointJoinBoundary_extension {X : SSet.{u}}
    {x : X _⦋0⦌} (hx : IsTerminalVertex x) (n : ℕ)
    (G : join (Δ[0] : SSet.{u}) (boundary n) ⟶ X)
    (hG : joinInr Δ[0] (boundary n : SSet.{u}) ≫ G = SSet.const x) :
    ∃ H : join (Δ[0] : SSet.{u}) Δ[n] ⟶ X,
      joinMap (𝟙 Δ[0]) (boundary n).ι ≫ H = G ∧
        joinInr Δ[0] Δ[n] ≫ H = SSet.const x := by
  let Z : SSet.{u} := boundary 0
  haveI (A : SSet.{u}) : IsIso (joinInr (boundary 0 : SSet.{u}) A) := by
    rw [boundary_zero, ← emptyJoinIso_inv (Δ[0] : SSet.{u}) A]
    infer_instance
  let W : join Z Δ[n] ⟶ X := SSet.const x
  have hw : joinMap (boundary 0).ι (𝟙 (boundary n : SSet.{u})) ≫ G =
      joinMap (𝟙 Z) (boundary n).ι ≫ W := by
    apply (cancel_epi (joinInr Z (boundary n : SSet.{u}))).1
    rw [← Category.assoc, joinInr_joinMap, Category.id_comp, hG]
    dsimp [W]
  let hs := (joinUnion_isPushout (boundary 0 : (Δ[0] : SSet.{u}).Subcomplex) (boundary n)).flip
  let T := hs.desc G W hw
  let e := boundaryJoinIso.{u} 0 n
  let v := SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (Fin.last n))
  let V := v ≫ joinInr Z Δ[n] ≫
    joinUnionLeft (boundary 0) (boundary n)
  have hV : V ≫ e.hom = boundaryVertex (0 + n) (Fin.last (0 + n + 1)) := by
    apply (cancel_mono (boundary (0 + n + 1)).ι).1
    dsimp [V, e]
    simp only [Category.assoc, boundaryJoinIso_hom_ι, boundaryVertex_ι]
    rw [← Category.assoc (joinUnionLeft (boundary 0) (boundary n)), joinUnionLeft_ι,
      ← Category.assoc (joinInr Z Δ[n]), joinInr_joinMap, Category.id_comp]
    exact joinStdSimplexIso_inr_lastVertex n
  have hlast : boundaryVertex (0 + n) (Fin.last (0 + n + 1)) ≫ (e.inv ≫ T) =
      SSet.yonedaEquiv.symm x := by
    rw [← hV, Category.assoc, Iso.hom_inv_id_assoc]
    dsimp [V, T]
    rw [Category.assoc, Category.assoc, hs.inr_desc]
    dsimp [W]
    rw [SSet.yonedaEquiv_symm_zero]
  obtain ⟨F, hF⟩ := hx (0 + n) (e.inv ≫ T) hlast
  have hT : (joinUnion (boundary 0) (boundary n)).ι ≫
      ((joinStdSimplexIso 0 n).hom ≫ F) = T := by
    rw [← Category.assoc, ← boundaryJoinIso_hom_ι, Category.assoc, hF,
      Iso.hom_inv_id_assoc]
  refine ⟨(joinStdSimplexIso 0 n).hom ≫ F, ?_, ?_⟩
  · have hh := congrArg (fun t ↦ joinUnionRight (boundary 0) (boundary n) ≫ t) hT
    rw [← Category.assoc, joinUnionRight_ι] at hh
    exact hh.trans (hs.inl_desc G W hw)
  · have hh := congrArg (fun t ↦ joinInr Z Δ[n] ≫
        joinUnionLeft (boundary 0) (boundary n) ≫ t) hT
    rw [← Category.assoc (joinUnionLeft _ _), joinUnionLeft_ι,
      ← Category.assoc, joinInr_joinMap, Category.id_comp] at hh
    rw [hs.inr_desc] at hh
    dsimp [W] at hh
    exact hh

/-- 概要：始対象を持つ left fibration の終対象上の fiber は可縮な Kan 複体。
方針：fiber の境界上に始対象からの錐を作り、基底の錐を終対象で充填して左ホーンで持ち上げる。
規約：元・標的の quasicategory 性は不要。
使われ方：Kerodon §7.1.5 の cocartesian な輸送による終対象の判定。 -/
lemma leftFibration_terminalFiber_isContractibleKan {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {e : E _⦋0⦌} (he : IsInitialVertex e)
    {b : B _⦋0⦌} (hb : IsTerminalVertex b) :
    IsContractibleKan (vertexFiber p b) := by
  intro n f
  obtain ⟨C, hC⟩ := he.exists_cosliceLift (f ≫ vertexFiberι p b)
  let G := sliceUnderUncurry C
  have hG : joinInr Δ[0] (boundary n : SSet.{u}) ≫ (G ≫ p) = SSet.const b := by
    dsimp [G]
    rw [← Category.assoc, sliceUnderUncurry_projection, hC, Category.assoc,
      vertexFiberι_comp, SSet.comp_const]
  obtain ⟨H, hH, hright⟩ := hb.exists_pointJoinBoundary_extension n (G ≫ p) hG
  let σ := (initialPointHornJoinIso n).inv ≫ G
  let β := (pointJoinStdSimplexIso n).inv ≫ H
  have hw : σ ≫ p = (horn (n + 1) 0).ι ≫ β := by
    dsimp [σ, β]
    rw [Category.assoc, ← hH]
    have hi := initialPointHornJoinIso_hom_ι n
    have hi' := congrArg (fun t ↦ (initialPointHornJoinIso n).inv ≫ t ≫
      (pointJoinStdSimplexIso n).inv) hi
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] at hi'
    rw [← Category.assoc, ← hi', Category.assoc]
  have := LeftFibration.mem (p := p) _
    (leftHornInclusions.intro (0 : Fin (n + 2)) (by change 0 < n + 1; omega))
  let sq : CommSq σ (horn (n + 1) 0).ι p β := ⟨hw⟩
  let T := (pointJoinStdSimplexIso n).hom ≫ sq.lift
  have hleft : joinMap (𝟙 Δ[0]) (boundary n).ι ≫ T = G := by
    dsimp [T]
    rw [← Category.assoc, ← initialPointHornJoinIso_hom_ι, Category.assoc, sq.fac_left]
    dsimp [σ]
    rw [Iso.hom_inv_id_assoc]
  have hTp : T ≫ p = H := by
    dsimp [T]
    rw [Category.assoc, sq.fac_right]
    dsimp [β]
    rw [Iso.hom_inv_id_assoc]
  let F := joinInr (Δ[0] : SSet.{u}) Δ[n] ≫ T
  have hFp : F ≫ p = SSet.const b := by
    dsimp [F]
    rw [Category.assoc, hTp, hright]
  refine ⟨vertexFiberLift p b F hFp, ?_⟩
  apply vertexFiber_hom_ext p b
  rw [Category.assoc, vertexFiberLift_ι]
  dsimp [F]
  rw [← Category.assoc, ← joinInr_joinMap (𝟙 (Δ[0] : SSet.{u})) (boundary n).ι,
    Category.assoc, hleft]
  exact (sliceUnderUncurry_projection C).trans hC

end SerrePositivity.InfinityCategories
