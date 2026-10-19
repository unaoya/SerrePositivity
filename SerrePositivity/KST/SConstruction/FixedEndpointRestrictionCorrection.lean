module
public import SerrePositivity.InfinityCategories.Core.MappingSpaceFibration
public import SerrePositivity.InfinityCategories.Core.KanFibrationTools
public import SerrePositivity.InfinityCategories.F1B.KanHomotopyClasses
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering

/-! # 固定端点の変換を単射部分上の指定した辺へ補正する
概要：部分上で同じホモトピー圏の射を表す変換へ、全体の変換を厳密に補正する。
方針：前合成による右写像空間の Kan fibration で、指定した頂点への経路を持ち上げる。
規約：標的は任意の quasicategory。元の始点・終点の図式は厳密に保つ。
使われ方：元の構造射を頂点部分上の縦辺として指定する全体補正。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 右写像空間の頂点による辺の表示は後合成に関して自然。 -/
lemma diagramPinchedVertex_map {X Y : SSet.{u}} (p : X ⟶ Y) {x y : X _⦋0⦌}
    (s : (pinchedHom x y) _⦋0⦌) :
    pinchedHomVertexEquiv _ _ ((pinchedHomMap p x y).app (Opposite.op ⦋0⦌) s) =
      (pinchedHomVertexEquiv x y s).map ((truncation 2).map p) := by
  apply SSet.Truncated.Edge.ext
  rfl

/-- 元の全体の変換の制限と同じ射を表す部分変換は、端点を保って厳密に回収できる。 -/
lemma exists_fixedEndpoint_restriction_correction {A D X : SSet.{u}} [Quasicategory X]
    (i : D ⟶ A) [Mono i] {F G : A ⟶ X} (H : SSet.Homotopy F G)
    (K : SSet.Homotopy (i ≫ F) (i ≫ G))
    (h : SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp H i)) =
        SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy K)) :
    ∃ H' : SSet.Homotopy F G, (i ▷ (Δ[1] : SSet.{u})) ≫ H'.h = K.h ∧
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H') =
        SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) := by
  let p := (pre i).app X
  let a := (pinchedHomVertexEquiv (functorVertex F) (functorVertex G)).symm
    (functorEdgeOfSimplicialHomotopy H)
  let b := (pinchedHomVertexEquiv (functorVertex (i ≫ F)) (functorVertex (i ≫ G))).symm
    (functorEdgeOfSimplicialHomotopy K)
  let q := pinchedHomMap p (functorVertex F) (functorVertex G)
  have he : pinchedHomVertexEquiv _ _ (q.app (Opposite.op ⦋0⦌) a) =
      functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp H i) := by
    rw [diagramPinchedVertex_map, Equiv.apply_symm_apply]
    rfl
  have hc : SSet.π₀.mk (q.app (Opposite.op ⦋0⦌) a) = SSet.π₀.mk b := by
    apply pinchedHomPiZeroToHom_injective (functorVertex (i ≫ F)) (functorVertex (i ≫ G))
    change SSet.Truncated.HomotopyCategory.homMk (pinchedHomVertexEquiv _ _ _) =
      SSet.Truncated.HomotopyCategory.homMk (pinchedHomVertexEquiv _ _ b)
    have hb : pinchedHomVertexEquiv (functorVertex (i ≫ F)) (functorVertex (i ≫ G)) b =
        functorEdgeOfSimplicialHomotopy K := Equiv.apply_symm_apply _ _
    exact ((congrArg SSet.Truncated.HomotopyCategory.homMk he).trans h).trans
      (congrArg SSet.Truncated.HomotopyCategory.homMk hb).symm
  obtain ⟨e⟩ := nonempty_vertexIso_of_piZero_eq hc
  obtain ⟨β, _⟩ := homotopyCategory_homMk_surjective _ _ e.hom
  obtain ⟨l, hl, hlq⟩ := leftFibration_liftEdge_source q a β
  let a' := (pinchedHom (functorVertex F) (functorVertex G)).δ 0 (SSet.yonedaEquiv l)
  have hq : q.app (Opposite.op ⦋0⦌) a' = b := by
    change q.app (Opposite.op ⦋0⦌)
      ((pinchedHom (functorVertex F) (functorVertex G)).δ 0 (SSet.yonedaEquiv l)) = b
    rw [δ_naturality_apply, ← SSet.yonedaEquiv_comp, hlq]
    exact (congrArg (fun z => (pinchedHom (functorVertex (i ≫ F))
      (functorVertex (i ≫ G))).δ 0 z) (SSet.yonedaEquiv.apply_symm_apply β.edge)).trans β.tgt_eq
  let e' := pinchedHomVertexEquiv (functorVertex F) (functorVertex G) a'
  have her : e'.map ((truncation 2).map p) = functorEdgeOfSimplicialHomotopy K := by
    rw [← diagramPinchedVertex_map, hq]
    exact Equiv.apply_symm_apply _ _
  refine ⟨simplicialHomotopyOfFunctorEdge e', ?_, ?_⟩
  ·
    have hh : SSet.yonedaEquiv.symm e'.edge ≫ p = curry K.h := by
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
      exact congrArg SSet.Truncated.Edge.edge her
    change (i ▷ (Δ[1] : SSet.{u})) ≫ uncurry (SSet.yonedaEquiv.symm e'.edge) = K.h
    rw [← uncurry_pre_app]
    exact (congrArg uncurry hh).trans (uncurry_curry K.h)
  · have γ : (pinchedHom (functorVertex F) (functorVertex G)).Edge a a' :=
      SSet.Edge.mk (SSet.yonedaEquiv l) (by
        rw [← stdSimplex.yonedaEquiv_δ_comp, hl]
        exact SSet.yonedaEquiv.apply_symm_apply _) rfl
    have hp := congrArg (pinchedHomPiZeroToHom (functorVertex F) (functorVertex G)) (SSet.π₀.sound γ)
    change SSet.Truncated.HomotopyCategory.homMk (pinchedHomVertexEquiv _ _ a) =
      SSet.Truncated.HomotopyCategory.homMk e' at hp
    have ha : pinchedHomVertexEquiv (functorVertex F) (functorVertex G) a =
        functorEdgeOfSimplicialHomotopy H := Equiv.apply_symm_apply _ _
    have hr : functorEdgeOfSimplicialHomotopy (simplicialHomotopyOfFunctorEdge e') = e' := by
      ext
      change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm e'.edge))) = e'.edge
      rw [curry_uncurry, Equiv.apply_symm_apply]
    rw [hr]
    exact hp.symm.trans (congrArg SSet.Truncated.HomotopyCategory.homMk ha)

end SerrePositivity.KST.SConstruction
