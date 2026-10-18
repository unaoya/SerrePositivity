module

public import SerrePositivity.InfinityCategories.Core.CocartesianCoslice
public import SerrePositivity.InfinityCategories.Core.PointHornJoin

/-!
概要：cocartesian な辺で始まる coslice の境界の相対充填。
方針：点と境界の join を最初の外側ホーンに直す。
規約：正次元の境界の最初の頂点の辺を指定する。
使われ方：Kerodon §5.1.1 の cocartesian な輸送の可縮性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：最初の頂点が cocartesian な辺を表す coslice の境界は基底上で充填できる。
方針：点と境界の join を最初のホーンに変換して指定された辺の充填性を適用する。
規約：p のファイブレーション性や quasicategory 性は不要。
使われ方：Kerodon §5.1.1 の cocartesian な輸送の相対充填。 -/
lemma exists_coslice_boundary_lift_of_cocartesian_vertex {E B : SSet.{u}}
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) (n : ℕ)
    (f : (boundary (n + 1) : SSet.{u}) ⟶ sliceUnder a)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ sliceUnder (a ≫ p))
    (hw : f ≫ sliceUnderPostcomp a p = (boundary (n + 1)).ι ≫ b)
    (he : IsCocartesianCosliceVertex a p
      (SSet.yonedaEquiv (boundaryVertex n 0 ≫ f))) :
    ∃ F : (Δ[n + 1] : SSet.{u}) ⟶ sliceUnder a,
      (boundary (n + 1)).ι ≫ F = f ∧ F ≫ sliceUnderPostcomp a p = b := by
  let G := sliceUnderUncurry f
  let H := sliceUnderUncurry b
  let σ := (initialPointHornJoinIso (n + 1)).inv ≫ G
  let β := (pointJoinStdSimplexIso (n + 1)).inv ≫ H
  have hedge : σ.app (Opposite.op ⦋1⦌) (initialHornEdge n) =
      (pointCosliceVertexEdge a (SSet.yonedaEquiv (boundaryVertex n 0 ≫ f))).edge := by
    rw [← initialPointHornJoinIso_edge n, ← SSet.yonedaEquiv_comp]
    dsimp [σ]
    rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]
    change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
      joinMap (𝟙 Δ[0]) (boundaryVertex n 0) ≫ G) = _
    have hg := sliceUnderUncurry_precomp f (boundaryVertex n 0)
    rw [← hg]
    have hu : sliceUnderUncurry (boundaryVertex n 0 ≫ f) =
        (SSet.yonedaEquiv (boundaryVertex n 0 ≫ f)).val := by
      simpa only [Equiv.symm_apply_apply] using
        sliceUnderUncurry_yoneda 0 (SSet.yonedaEquiv (boundaryVertex n 0 ≫ f))
    exact congrArg (fun t ↦ SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ t)) hu
  have hsquare : σ ≫ p = (horn (n + 2) 0).ι ≫ β := by
    have hh := congrArg sliceUnderUncurry hw
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_precomp] at hh
    dsimp [σ, β, G, H]
    rw [Category.assoc, hh]
    have hi := initialPointHornJoinIso_hom_ι (n + 1)
    have hi' := congrArg (fun t ↦ (initialPointHornJoinIso (n + 1)).inv ≫ t ≫
      (pointJoinStdSimplexIso (n + 1)).inv) hi
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] at hi'
    rw [← Category.assoc, ← hi', Category.assoc]
  obtain ⟨L, hL, hp⟩ := he n σ β hedge hsquare
  let T := (pointJoinStdSimplexIso (n + 1)).hom ≫ L
  have hleft : joinMap (𝟙 Δ[0]) (boundary (n + 1)).ι ≫ T = G := by
    dsimp [T]
    rw [← Category.assoc, ← initialPointHornJoinIso_hom_ι, Category.assoc, hL]
    dsimp [σ]
    rw [Iso.hom_inv_id_assoc]
  have hfixed : joinInl Δ[0] Δ[n + 1] ≫ T = a := by
    have hh := congrArg (fun t ↦ joinInl Δ[0] (boundary (n + 1) : SSet.{u}) ≫ t) hleft
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp] at hh
    exact hh.trans (sliceUnderUncurry_fixed f)
  refine ⟨sliceUnderCurry T hfixed, ?_, ?_⟩
  · apply sliceUnderUncurry_injective a
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
    exact hleft
  · apply sliceUnderUncurry_injective (a ≫ p)
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_curry]
    dsimp [T]
    rw [Category.assoc, hp]
    dsimp [β]
    rw [Iso.hom_inv_id_assoc]

/-- 概要：点の coslice の頂点は対応する辺の一次単体で決まる。
方針：Yoneda 同値と標準辺の同型を消去する。
規約：辺の端点の表示は問わない。
使われ方：Kerodon §5.1.1 の輸送の基底との一致。 -/
lemma pointCosliceVertexEdge_injective {E : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E)
    {s t : (sliceUnder a) _⦋0⦌}
    (h : (pointCosliceVertexEdge a s).edge = (pointCosliceVertexEdge a t).edge) : s = t := by
  apply Subtype.ext
  apply (cancel_epi (joinStdSimplexIso 0 0).inv).1
  exact SSet.yonedaEquiv.injective h

/-- 概要：基底の点の coslice の各頂点は cocartesian な頂点へ持ち上がる。
方針：対応する基底の辺を始点を指定して持ち上げ、coslice の頂点へ戻す。
規約：cocartesian fibration の辺の存在条件だけを使う。
使われ方：Kerodon §5.1.4 の輸送の選択の存在。 -/
lemma exists_cocartesianCosliceVertex_lift {E B : SSet.{u}}
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) [CocartesianHornFibration p]
    (s : (sliceUnder (a ≫ p)) _⦋0⦌) :
    ∃ t : (sliceUnder a) _⦋0⦌, IsCocartesianCosliceVertex a p t ∧
      (sliceUnderPostcomp a p).app (Opposite.op ⦋0⦌) t = s := by
  let d := pointCosliceVertexEdge (a ≫ p) s
  let d' : SSet.Truncated.Edge (X := (truncation 2).obj B)
      (p.app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv a))
      ((sliceUnderProjection (a ≫ p)).app (Opposite.op ⦋0⦌) s) :=
    { edge := d.edge
      src_eq := by
        have hs : B.δ 1 d.edge = SSet.yonedaEquiv (a ≫ p) := d.src_eq
        change B.δ 1 d.edge = _
        rw [hs, SSet.yonedaEquiv_comp]
      tgt_eq := d.tgt_eq }
  obtain ⟨y, e, hp, he⟩ := CocartesianHornFibration.exists_lift (p := p)
    (SSet.yonedaEquiv a) _ d'
  refine ⟨pointCosliceVertexOfEdge a e, ?_, ?_⟩
  · exact (hasCocartesianHornLifting_congr p (pointCosliceVertexEdge_ofEdge a e)).2 he
  · apply pointCosliceVertexEdge_injective (a ≫ p)
    rw [pointCosliceVertexEdge_postcomp, pointCosliceVertexEdge_ofEdge]
    exact hp

/-- 概要：cocartesian な辺の coslice から基底の点の coslice への射影は trivial Kan fibration。
方針：零次元では辺を持ち上げ、正次元では最初の頂点の cocartesian 性で境界を充填する。
規約：cocartesian fibration の仮定だけで、quasicategory 性は不要。
使われ方：Kerodon §5.1.4 の輸送の選択の可縮性。 -/
instance cocartesianCosliceProjection_trivialKanFibration {E B : SSet.{u}}
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) [CocartesianHornFibration p] :
    TrivialKanFibration (cocartesianCosliceProjection a p) := by
  rw [trivialKanFibration_iff_boundary]
  intro n
  constructor
  intro f b sq
  cases n with
  | zero =>
    obtain ⟨t, ht, hp⟩ := exists_cocartesianCosliceVertex_lift a p (SSet.yonedaEquiv b)
    let t' : (cocartesianCoslice a p) _⦋0⦌ := ⟨t, by
      intro v
      have hv : v = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
      simpa only [hv, op_id, CategoryTheory.Functor.map_id_apply] using ht⟩
    refine CommSq.HasLift.mk' {
      l := SSet.yonedaEquiv.symm t'
      fac_left := boundary.hom_ext₀
      fac_right := ?_ }
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hp
  | succ n =>
    let f' := f ≫ cocartesianCosliceι a p
    have hw : f' ≫ sliceUnderPostcomp a p = (boundary (n + 1)).ι ≫ b := sq.w
    have he : IsCocartesianCosliceVertex a p
        (SSet.yonedaEquiv (boundaryVertex n 0 ≫ f')) := by
      exact fullSubcomplexOnVertices_vertex
        (SSet.yonedaEquiv (boundaryVertex n 0 ≫ f))
    obtain ⟨F, hF, hp⟩ := exists_coslice_boundary_lift_of_cocartesian_vertex a p n f' b hw he
    have hv (v : ⦋0⦌ ⟶ ⦋n + 1⦌) :
        IsCocartesianCosliceVertex a p (SSet.yonedaEquiv (stdSimplex.map v ≫ F)) := by
      have he : stdSimplex.map v =
          boundaryVertex n (v.toOrderHom 0) ≫ (boundary (n + 1)).ι := by
        rw [boundaryVertex_ι]
        apply SSet.yonedaEquiv.injective
        rw [Equiv.apply_symm_apply]
        apply stdSimplex.ext
        intro i
        fin_cases i
        rfl
      rw [he, Category.assoc, hF]
      exact fullSubcomplexOnVertices_vertex
        (SSet.yonedaEquiv (boundaryVertex n (v.toOrderHom 0) ≫ f))
    let L := fullSubcomplexLiftSimplex (IsCocartesianCosliceVertex a p) F hv
    have hL : L ≫ cocartesianCosliceι a p = F := rfl
    refine CommSq.HasLift.mk' { l := L, fac_left := ?_, fac_right := ?_ }
    · apply (cancel_mono (fullSubcomplexOnVertices (sliceUnder a)
        (IsCocartesianCosliceVertex a p)).ι).1
      change (boundary (n + 1)).ι ≫ L ≫ cocartesianCosliceι a p = f'
      rw [hL]
      exact hF
    · change L ≫ cocartesianCosliceι a p ≫ sliceUnderPostcomp a p = b
      rw [← Category.assoc, hL]
      exact hp

end SerrePositivity.InfinityCategories
