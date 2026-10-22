module
public import SerrePositivity.InfinityCategories.Stable.ZeroCornerSquareConeModel
public import SerrePositivity.InfinityCategories.Stable.UniversalConeChoiceProjection

/-!
概要：零隅四角形と同じ cospan 上の錐の実比較。
方針：全部分複体・引き戻し・形状同型を全単体で照合する。
規約：安定性・余極限は先取りしない。使われ方：一般安定性判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ実図式の比較 `loopDiagramUniversalConeLift`。 -/
def loopDiagramUniversalConeLift (X : SSet.{u}) [Quasicategory X] :
    loopDiagrams X ⟶ universalConesOver
      (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
        IsZeroOuterCospanVertex).ι :=
  pullback.lift (loopDiagramConeFamily X) (loopDiagramZeroOuterCospan X) rfl

/-- 同じ実図式の比較 `zeroOuterUniversalConeSquare`。 -/
def zeroOuterUniversalConeSquare (X : SSet.{u}) :
    universalConesOver
      (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
        IsZeroOuterCospanVertex).ι ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X :=
  pullback.fst _ _ ≫
    (relativeTerminalVertices (coneRestriction (horn 2 2 : SSet.{u}) X)).ι ≫
      (pre cospanConeSquareIso.inv).app X

/-- 同じ実図式の比較 `zeroOuterUniversalConeSquare_input`。 -/
lemma zeroOuterUniversalConeSquare_input (X : SSet.{u}) :
    zeroOuterUniversalConeSquare X ≫ (pre cospanSquareBoundary).app X =
      pullback.snd (limitConeProjection (horn 2 2 : SSet.{u}) X)
        (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
          IsZeroOuterCospanVertex).ι ≫
        (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
          IsZeroOuterCospanVertex).ι := by
  dsimp only [zeroOuterUniversalConeSquare, cospanSquareBoundary]
  simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, Iso.hom_inv_id,
    Category.comp_id]
  exact pullback.condition (f := limitConeProjection (horn 2 2 : SSet.{u}) X)
    (g := (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
      IsZeroOuterCospanVertex).ι)

/-- 同じ実図式の比較 `zeroOuterUniversalConeSquare_isLoop`。 -/
lemma zeroOuterUniversalConeSquare_isLoop (X : SSet.{u}) [Quasicategory X]
    (v : (universalConesOver
      (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
        IsZeroOuterCospanVertex).ι) _⦋0⦌) :
    IsLoopDiagramVertex ((zeroOuterUniversalConeSquare X).app (Opposite.op ⦋0⦌) v) := by
  let F := zeroOuterUniversalConeSquare X
  have hzero : IsZeroOuterCospanVertex
      (((pre cospanSquareBoundary).app X).app (Opposite.op ⦋0⦌)
        (F.app (Opposite.op ⦋0⦌) v)) := by
    have he := ConcreteCategory.congr_hom
      (NatTrans.congr_app (zeroOuterUniversalConeSquare_input X) (Opposite.op ⦋0⦌)) v
    change ((F ≫ (pre cospanSquareBoundary).app X).app (Opposite.op ⦋0⦌)) v = _ at he
    change IsZeroOuterCospanVertex (((F ≫ (pre cospanSquareBoundary).app X).app
      (Opposite.op ⦋0⦌)) v)
    rw [he]
    exact fullSubcomplexOnVertices_vertex
      ((pullback.snd (limitConeProjection (horn 2 2 : SSet.{u}) X)
        (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
          IsZeroOuterCospanVertex).ι).app (Opposite.op ⦋0⦌) v)
  have hz := (zeroOuterCospanVertex_square_iff (F.app (Opposite.op ⦋0⦌) v)).mp hzero
  refine ⟨hz.2, hz.1, ?_⟩
  let w := (pullback.fst (limitConeProjection (horn 2 2 : SSet.{u}) X)
    (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
      IsZeroOuterCospanVertex).ι).app (Opposite.op ⦋0⦌) v
  let f := (functorVertexEquiv _ _).symm w.val
  let c : JoinCone (joinInr (Δ[0] : SSet.{u}) (horn 2 2 : SSet.{u}) ≫ f) := ⟨f, rfl⟩
  have hc : IsLimitCone c := by
    apply isLimitCone_of_terminalBoundaryLifting_coneRestriction c
    change TerminalBoundaryLifting _ (functorVertex f)
    have hf : functorVertex f = w.val := (functorVertexEquiv _ _).apply_symm_apply w.val
    rw [hf]
    exact fullSubcomplexOnVertices_vertex w
  change IsPullbackSquare (cospanConeSquareIso.inv ≫ f)
  exact coneSquare_isPullback c hc

/-- 同じ実図式の比較 `zeroOuterUniversalConeToLoop`。 -/
def zeroOuterUniversalConeToLoop (X : SSet.{u}) [Quasicategory X] :
    universalConesOver
      (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
        IsZeroOuterCospanVertex).ι ⟶ loopDiagrams X :=
  fullSubcomplexLift IsLoopDiagramVertex (zeroOuterUniversalConeSquare X)
    (zeroOuterUniversalConeSquare_isLoop X)

/-- 同じ実図式の比較 `loopDiagramUniversalConeIso`。 -/
def loopDiagramUniversalConeIso (X : SSet.{u}) [Quasicategory X] :
    loopDiagrams X ≅ universalConesOver
      (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
        IsZeroOuterCospanVertex).ι where
  hom := loopDiagramUniversalConeLift X
  inv := zeroOuterUniversalConeToLoop X
  hom_inv_id := by
    apply (cancel_mono (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι).1
    simp only [Category.assoc, zeroOuterUniversalConeToLoop, fullSubcomplexLift_ι,
      Category.id_comp]
    rw [zeroOuterUniversalConeSquare, ← Category.assoc,
      loopDiagramUniversalConeLift, pullback.lift_fst, ← Category.assoc,
      loopDiagramConeFamily_ι]
    simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id,
      pre_id, NatTrans.id_app, Category.comp_id]
  inv_hom_id := by
    apply (cancel_mono (pullback.fst (limitConeProjection (horn 2 2 : SSet.{u}) X)
      (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
        IsZeroOuterCospanVertex).ι)).1
    rw [Category.assoc, loopDiagramUniversalConeLift, pullback.lift_fst, Category.id_comp]
    apply (cancel_mono
      (relativeTerminalVertices (coneRestriction (horn 2 2 : SSet.{u}) X)).ι).1
    rw [Category.assoc, loopDiagramConeFamily_ι, ← Category.assoc]
    rw [zeroOuterUniversalConeToLoop, fullSubcomplexLift_ι, zeroOuterUniversalConeSquare]
    simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, Iso.hom_inv_id,
      pre_id, NatTrans.id_app, Category.comp_id]
end SerrePositivity.InfinityCategories
