module
public import SerrePositivity.KST.SConstruction.FunctorZeroEvaluation
public import SerrePositivity.KST.SConstruction.DegeneratePushouts
public import SerrePositivity.InfinityCategories.F1.ColimitCoconeEdges
public import SerrePositivity.InfinityCategories.F1.ColimitFullyFaithful

/-! # 異なる図式上の普遍余錐の比較
概要：同型な図式上の二つの普遍余錐は全余錐として同型。
方針：普遍余錐の射影のホモトピー圏での充満忠実性を使う。
規約：図式を厳密に等しいとは仮定しない。使われ方：零図式の押し出しと二方向補完。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：図式の同型は指定された普遍余錐全体の同型へ持ち上がる。
方針：普遍余錐の射影の充満忠実関手で同型の逆像を取る。
規約：全図式の余極限の存在は仮定しない。使われ方：零図式との比較。 -/
def colimitCoconeIsoOfDiagramIso {K C : SSet.{u}} [Quasicategory C]
    {p q : K ⟶ C} (c : JoinCocone p) (d : JoinCocone q)
    (hc : IsColimitCone c) (hd : IsColimitCone d) (e : FunctorIso p q) : FunctorIso c.val d.val := by
  let x := colimitCoconeVertex c hc
  let y := colimitCoconeVertex d hd
  let Q := (hoFunctor.map (colimitCoconeProjection K C)).toFunctor
  have ee : Q.obj (SSet.HomotopyCategory.mk x) ≅ Q.obj (SSet.HomotopyCategory.mk y) := by
    change VertexIso ((colimitCoconeProjection K C).app (Opposite.op ⦋0⦌) x)
      ((colimitCoconeProjection K C).app (Opposite.op ⦋0⦌) y)
    dsimp only [x, y]
    rw [colimitCoconeVertex_projection, colimitCoconeVertex_projection]
    exact e
  let E := (colimitCoconeProjectionHoFullyFaithful K C).preimageIso ee
  exact VertexIso.map E (relativeInitialVertices (coconeRestriction K C)).ι

/-- 概要：同型な入力 span を持つ押し出し四角形は全体として同型。
方針：普遍余錐の比較を正方形の同型で戻す。
規約：四頂点だけの同型に弱めない。使われ方：点ごとの cofiber 比較。 -/
def pushoutSquareIsoOfSpanIso {C : SSet.{u}} [Quasicategory C]
    (F G : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C)
    (hF : IsPushoutSquare F) (hG : IsPushoutSquare G)
    (e : FunctorIso (pushoutSpan F) (pushoutSpan G)) : FunctorIso F G := by
  let E := colimitCoconeIsoOfDiagramIso (pushoutCocone F) (pushoutCocone G) hF hG e
  have H := E.precomp spanCoconeSquareIso.inv
  change FunctorIso (spanCoconeSquareIso.inv ≫ spanCoconeSquareIso.hom ≫ F)
    (spanCoconeSquareIso.inv ≫ spanCoconeSquareIso.hom ≫ G) at H
  simpa only [Iso.inv_hom_id_assoc] using H

/-- 概要：全入力が零対象である押し出しの出力も零対象。
方針：定値零四角形と入力 span を比較し、押し出し四角形の同型を評価する。
規約：C は零対象を持つ quasicategory。使われ方：cofiber 補完後の零対角。 -/
lemma isZeroVertex_pushout_apex_of_zeroSpan {C : SSet.{u}} [Quasicategory C] [HasZeroVertex C]
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C) (hF : IsPushoutSquare F)
    (hp : ∀ a : (horn 2 0 : SSet.{u}) _⦋0⦌,
      IsZeroVertex ((pushoutSpan F).app (Opposite.op ⦋0⦌) a)) :
    IsZeroVertex (squareVertex F 1 1) := by
  let z := chosenZeroVertex C
  let Z : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C := SSet.const z.vertex
  have hZ : IsPushoutSquare Z := by
    have h := isPushoutSquare_fst (SSet.const z.vertex : (Δ[1] : SSet.{u}) ⟶ C)
    rwa [SSet.comp_const] at h
  have hpZ : IsZeroVertex (functorVertex (pushoutSpan Z)) := by
    change IsZeroVertex (functorVertex (spanSquareBoundary ≫ SSet.const z.vertex))
    rw [SSet.comp_const]
    exact functor_const_isZeroVertex z.vertex z.isZero
  have hpF := isZeroVertex_functorVertex_of_pointwise (pushoutSpan F) hp
  let e : FunctorIso (pushoutSpan Z) (pushoutSpan F) :=
    zeroVertexIso ⟨_, hpZ.1, hpZ.2⟩ ⟨_, hpF.1, hpF.2⟩
  let E := pushoutSquareIsoOfSpanIso Z F hZ hF e
  have ea := VertexIso.map E (evaluateFunctorAt
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
  rw [evaluateFunctorAt_functorVertex, evaluateFunctorAt_functorVertex] at ea
  have hz : IsZeroVertex (squareVertex Z 1 1) := by
    change IsZeroVertex (PinchedHom.constant z.vertex 0)
    rw [pinchedConstant_zero]
    exact z.isZero
  exact hz.of_vertexIso ea

end SerrePositivity.KST.SConstruction
