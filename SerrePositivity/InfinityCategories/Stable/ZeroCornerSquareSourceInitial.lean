module
public import SerrePositivity.InfinityCategories.Stable.ZeroOuterConeSourceInitial

/-!
概要：普遍錐の選択を忘れ、全零隅四角形の始対象を得る。
方針：元の実引き戻しの同型と同じ頂点 fiber の比較を接続する。
規約：安定性・余極限は仮定しない。使われ方：一般安定性判定の押し出し構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ固定頂点を保つ錐の比較 `coneInputFullSubcomplexIso_hom_fst`。 -/
lemma coneInputFullSubcomplexIso_hom_fst {E B : SSet.{u}} (f : E ⟶ B)
    (Q : B _⦋0⦌ → Prop) :
    (coneInputFullSubcomplexIso f Q).hom ≫ pullback.fst f (fullSubcomplexOnVertices B Q).ι =
      (fullSubcomplexOnVertices E (fun v ↦ Q (f.app (Opposite.op ⦋0⦌) v))).ι :=
  pullback.lift_fst _ _ _

/-- 同じ固定頂点を保つ錐の比較 `zeroCornerSquareConeIso_diagram`。 -/
lemma zeroCornerSquareConeIso_diagram (X : SSet.{u}) :
    (zeroCornerSquareConeIso X).hom ≫
      pullback.fst (coneRestriction (horn 2 2 : SSet.{u}) X)
        (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
          IsZeroOuterCospanVertex).ι =
      (fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
        IsZeroCornerSquareVertex).ι ≫ (squareConeFunctorIso X).hom := by
  dsimp only [zeroCornerSquareConeIso, Iso.trans_hom]
  rw [Category.assoc, coneInputFullSubcomplexIso_hom_fst, fullSubcomplexIso_hom_ι]

/-- 同じ固定頂点を保つ錐の比較 `squareConeFunctorIso_apex`。 -/
lemma squareConeFunctorIso_apex (X : SSet.{u}) :
    (squareConeFunctorIso X).hom ≫ coneApexEvaluation (horn 2 2 : SSet.{u}) X =
      evaluateFunctorAt (Y := X)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  dsimp only [squareConeFunctorIso, coneApexEvaluation]
  rw [stable_pre_evaluateFunctorAt]
  have hp := congrArg (fun q ↦ q.app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) cospanConeSquareIso_initialPoint.{u}
  change cospanConeSquareIso.hom.app (Opposite.op ⦋0⦌)
      ((joinInl (Δ[0] : SSet.{u}) (horn 2 2 : SSet.{u})).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = _ at hp
  rw [hp]
  rfl

/-- 同じ固定頂点を保つ錐の比較 `zeroCornerSquareSource`。 -/
def zeroCornerSquareSource (X : SSet.{u}) : zeroCornerSquares X ⟶ X :=
  (fullSubcomplexOnVertices _ IsZeroCornerSquareVertex).ι ≫
    evaluateFunctorAt
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2))

/-- 同じ固定頂点を保つ錐の比較 `zeroCornerSquareConeIso_source`。 -/
lemma zeroCornerSquareConeIso_source (X : SSet.{u}) :
    (zeroCornerSquareConeIso X).hom ≫
      (pullback.fst (coneRestriction (horn 2 2 : SSet.{u}) X)
        (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
          IsZeroOuterCospanVertex).ι ≫ coneApexEvaluation (horn 2 2 : SSet.{u}) X) =
      zeroCornerSquareSource X := by
  rw [← Category.assoc, zeroCornerSquareConeIso_diagram, Category.assoc,
    squareConeFunctorIso_apex]
  rfl

/-- 同じ固定頂点を保つ錐の比較 `zeroCornerSquareSourceFiber_hasInitial`。 -/
lemma zeroCornerSquareSourceFiber_hasInitial {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] [HasFiniteLimits X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) (x : X _⦋0⦌) :
    ∃ v : (vertexFiber (zeroCornerSquareSource X) x) _⦋0⦌, IsInitialVertex v := by
  let q := pullback.fst (coneRestriction (horn 2 2 : SSet.{u}) X)
    (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
      IsZeroOuterCospanVertex).ι ≫ coneApexEvaluation (horn 2 2 : SSet.{u}) X
  let f := vertexFiberMap (zeroCornerSquareSource X) q (zeroCornerSquareConeIso X).hom
    (zeroCornerSquareConeIso_source X) x
  have : IsIso f := HomotopyLimits.vertexFiberMap_isIso _ _ _ _ _
  obtain ⟨v, hv⟩ := zeroOuterConeSourceFiber_hasInitial s hs hΩ x
  have ht := hv.map_of_isIso (inv f)
  exact ⟨(inv f).app (Opposite.op ⦋0⦌) v, ht⟩
end SerrePositivity.InfinityCategories
