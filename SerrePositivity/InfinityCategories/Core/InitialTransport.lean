module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.InitialHomotopy
public import SerrePositivity.InfinityCategories.Core.TerminalTransport
public import SerrePositivity.InfinityCategories.Core.PointHornJoin
public import SerrePositivity.InfinityCategories.Core.OuterHornDuality

/-! General declarations moved verbatim from their original modules. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet
open scoped Simplicial

/-- 概要：始頂点の coslice 射影に任意の図式を持ち上げられる。
方針：空部分複体からの持ち上げ性を使う。
規約：図式の形状は任意。使われ方：境界からの余錐と零対象からの図式。 -/
lemma IsInitialVertex.exists_stableCosliceLift {A X : SSet.{u}} {x : X _⦋0⦌}
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


/-- 概要：始対象が存在する場合、ホモトピー圏で始対象となる頂点は始対象。
方針：境界を既知の始対象からの余錐にし、最初の辺が同型となる外側ホーンを充填する。
規約：quasicategory 性を仮定する。
使われ方：HTT §1.2.12、Kerodon §4.7.3 の同型不変性。 -/
lemma isInitialVertex_of_isInitialHo {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (hx : IsInitialVertex x)
    (hy : IsInitial (SSet.HomotopyCategory.mk y : hoFunctor.obj X)) : IsInitialVertex y := by
  intro n b hb
  obtain ⟨C, hC⟩ := hx.exists_stableCosliceLift b
  let G := sliceUnderUncurry C
  let v := SSet.yonedaEquiv (boundaryVertex n 0)
  let t := C.app (Opposite.op ⦋0⦌) v
  have ht : (sliceUnderProjection (SSet.yonedaEquiv.symm x)).app (Opposite.op ⦋0⦌) t = y := by
    change SSet.yonedaEquiv ((boundaryVertex n 0 ≫ C) ≫
      sliceUnderProjection (SSet.yonedaEquiv.symm x)) = y
    rw [Category.assoc, hC, hb, Equiv.apply_symm_apply]
  let e := sliceUnderVertexEdge x t
  have hs : IsInitial (SSet.HomotopyCategory.mk
      ((sliceUnderProjection (SSet.yonedaEquiv.symm x)).app (Opposite.op ⦋0⦌) t) :
        hoFunctor.obj X) := by rw [ht]; exact hy
  have he : IsInvertibleEdge e := isIso_of_isInitial hx.isInitialHo hs _
  let σ := (initialPointHornJoinIso (n + 1)).inv ≫ G
  have hσ : σ.app (Opposite.op ⦋1⦌) (initialHornEdge n) = e.edge := by
    rw [← initialPointHornJoinIso_edge, ← SSet.yonedaEquiv_comp]
    change SSet.yonedaEquiv (((joinStdSimplexIso 0 0).inv ≫
      joinMap (𝟙 Δ[0]) (boundaryVertex n 0) ≫
        (initialPointHornJoinIso (n + 1)).hom) ≫
          ((initialPointHornJoinIso (n + 1)).inv ≫ G)) = _
    rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]
    change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
      (joinMap (𝟙 Δ[0]) (boundaryVertex n 0) ≫ sliceUnderUncurry C)) = _
    rw [← sliceUnderUncurry_precomp]
    rw [show boundaryVertex n 0 = SSet.yonedaEquiv.symm v from
      (SSet.yonedaEquiv.symm_apply_apply _).symm,
      SSet.yonedaEquiv_symm_comp,
      sliceUnderUncurry_yoneda]
    rfl
  obtain ⟨F, hF⟩ := hasInitialHornFillers_of_isInvertibleEdge e he n σ hσ
  refine ⟨stdSimplex.δ 0 ≫ F, ?_⟩
  have hG : joinMap (𝟙 Δ[0]) (boundary (n + 1)).ι ≫
      (pointJoinStdSimplexIso (n + 1)).hom ≫ F = G := by
    rw [← Category.assoc, ← initialPointHornJoinIso_hom_ι, Category.assoc, hF]
    exact (initialPointHornJoinIso (n + 1)).hom_inv_id_assoc G
  calc
    (boundary (n + 1)).ι ≫ stdSimplex.δ 0 ≫ F =
        joinInr Δ[0] (boundary (n + 1) : SSet.{u}) ≫ G := by
      rw [← hG]
      simp only [← Category.assoc]
      rw [joinInr_joinMap]
      simp only [Category.assoc]
      rw [← Category.assoc (joinInr _ _) (pointJoinStdSimplexIso (n + 1)).hom,
        pointJoinStdSimplexIso_inr]
    _ = b := by rw [sliceUnderUncurry_projection, hC]


/-- 概要：始対象性はホモトピー圏の頂点の同型で保たれる。
方針：h C の始対象を同型で移し、外側ホーンによる判定へ戻す。
規約：同型は h C で取る。使われ方：余極限の選択の比較。 -/
lemma IsInitialVertex.of_vertexIso {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (hx : IsInitialVertex x) (e : VertexIso x y) : IsInitialVertex y :=
  isInitialVertex_of_isInitialHo hx (hx.isInitialHo.ofIso e)


/-- 概要：同型な頂点の始対象性は同値。
方針：同型と逆同型で始対象性を移す。
規約：周囲は quasicategory。使われ方：選んだ始対象の置換。 -/
lemma isInitialVertex_iff_of_vertexIso {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (e : VertexIso x y) : IsInitialVertex x ↔ IsInitialVertex y :=
  ⟨fun h => h.of_vertexIso e, fun h => h.of_vertexIso e.symm⟩


/-- 概要：余極限性は図式上の coslice のホモトピー圏の同型で保たれる。
方針：coslice の始対象性に同型不変性を適用する。
規約：頂点だけでなく余錐全体の同型を仮定する。使われ方：余極限の選択の比較。 -/
lemma IsColimitCone.of_vertexIso {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    {c d : JoinCocone p} (hc : IsColimitCone c) (e : VertexIso (X := sliceUnder p) c d) :
    IsColimitCone d := IsInitialVertex.of_vertexIso hc e


/-- 概要：図式上で同型な余極限錐の余極限性は同値。
方針：coslice の始対象性の同値を使う。
規約：同型の場所は h(sliceUnder p)。使われ方：S3 の余極限の選択。 -/
lemma isColimitCone_iff_of_vertexIso {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    {c d : JoinCocone p} (e : VertexIso (X := sliceUnder p) c d) :
    IsColimitCone c ↔ IsColimitCone d := isInitialVertex_iff_of_vertexIso e


end SerrePositivity.InfinityCategories
