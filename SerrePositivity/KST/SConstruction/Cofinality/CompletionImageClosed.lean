module
public import SerrePositivity.KST.SConstruction.Cofinality.MultiCompletion
public import SerrePositivity.KST.LocalizingInvariants.CompletionCofiberWide
public import SerrePositivity.KST.SConstruction.ClosedPredicateOperations
public import SerrePositivity.InfinityCategories.Stable.PushoutCofiberRectangle

/-!
概要：同じ全多次数の指定完備化射の本質像を閉じた安定頂点条件として束ねる。
方針：元の本質像と実安定閉包の等号、および押し出しの二つの cofiber 列を使う。
規約：retract 閉包へ拡大せず、元の本質像を保持する。
使われ方：K-B2-S1 の閉じた安定部分圏入力への代入。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：同じ全多次数の本質像は指定された全押し出しで閉じる。
方針：押し出しに零終点を付加し、外側と右面の cofiber 列の閉性を使う。
規約：周囲の指定された押し出しの第四頂点そのものを回収する。
使われ方：本質像の閉じた安定条件の押し出し成分。 -/
lemma completionImage_pushout_mem (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : F2.Idempotent.IsIdempotentCompletion f.val)
    (L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (((multiSEndofunctor r).obj ι).obj Y).carrier)
    (hL : IsPushoutSquare L)
    (h00 : squareVertex L 0 0 ∈ LocalizingInvariants.completionEssentialImage
      (((multiSEndofunctor r).obj ι).map f).val)
    (h10 : squareVertex L 1 0 ∈ LocalizingInvariants.completionEssentialImage
      (((multiSEndofunctor r).obj ι).map f).val)
    (h01 : squareVertex L 0 1 ∈ LocalizingInvariants.completionEssentialImage
      (((multiSEndofunctor r).obj ι).map f).val) :
    squareVertex L 1 1 ∈ LocalizingInvariants.completionEssentialImage
      (((multiSEndofunctor r).obj ι).map f).val := by
  let F := ((multiSEndofunctor r).obj ι).map f
  let : IsExactFunctor F.val := stableModelHom_exact F
  let P := LocalizingInvariants.completionEssentialImage F.val
  have he := LocalizingInvariants.stableClosure_completionEssentialImage F.val
    (multiSEndofunctor_map_isIdempotentCompletion r ι f hf).2.1
  have hm (z) : StableVertexClosure P z ↔ z ∈ P :=
    Iff.of_eq (congrArg (fun Q => z ∈ Q) he)
  let t := chosenPushoutCofiberRectangle L hL
  have hA : squareVertex t.outerZeroTriangle.square 0 0 = squareVertex L 0 0 := by
    change squareVertex (pastingSquare t.diagram 2) 0 0 = _
    exact congrArg (fun D => squareVertex D 0 0) t.left_eq
  have hC : squareVertex t.outerZeroTriangle.square 1 0 = squareVertex L 0 1 := by
    change squareVertex (pastingSquare t.diagram 2) 0 1 = _
    exact congrArg (fun D => squareVertex D 0 1) t.left_eq
  have hB : squareVertex t.rightZeroTriangle.square 0 0 = squareVertex L 1 0 := by
    change squareVertex (pastingSquare t.diagram 2) 1 0 = _
    exact congrArg (fun D => squareVertex D 1 0) t.left_eq
  have hD : squareVertex t.rightZeroTriangle.square 1 0 = squareVertex L 1 1 := by
    change squareVertex (pastingSquare t.diagram 2) 1 1 = _
    exact congrArg (fun D => squareVertex D 1 1) t.left_eq
  have hE : StableVertexClosure P (squareVertex t.outerZeroTriangle.square 1 1) :=
    StableVertexClosure.of_cofiber t.outerZeroTriangle t.outer_isCofiber
      (hA.symm ▸ (hm _).mpr h00) (hC.symm ▸ (hm _).mpr h01)
  have hE' : StableVertexClosure P (squareVertex t.rightZeroTriangle.square 1 1) := hE
  exact (hm _).mp (hD ▸ StableVertexClosure.extension P t.rightZeroTriangle
    t.right_isCofiber (hB.symm ▸ (hm _).mpr h10) hE')

/-- 概要：同じ全多次数の本質像は指定された全引き戻しで閉じる。
方針：引き戻しを押し出しと読み、右面と外側の cofiber 列を逆順に使う。
規約：指定された第一頂点の像所属を結論する。
使われ方：本質像の閉じた安定条件の引き戻し成分。 -/
lemma completionImage_pullback_mem (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : F2.Idempotent.IsIdempotentCompletion f.val)
    (L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (((multiSEndofunctor r).obj ι).obj Y).carrier)
    (hL : IsPullbackSquare L)
    (h10 : squareVertex L 1 0 ∈ LocalizingInvariants.completionEssentialImage
      (((multiSEndofunctor r).obj ι).map f).val)
    (h01 : squareVertex L 0 1 ∈ LocalizingInvariants.completionEssentialImage
      (((multiSEndofunctor r).obj ι).map f).val)
    (h11 : squareVertex L 1 1 ∈ LocalizingInvariants.completionEssentialImage
      (((multiSEndofunctor r).obj ι).map f).val) :
    squareVertex L 0 0 ∈ LocalizingInvariants.completionEssentialImage
      (((multiSEndofunctor r).obj ι).map f).val := by
  let F := ((multiSEndofunctor r).obj ι).map f
  let : IsExactFunctor F.val := stableModelHom_exact F
  let P := LocalizingInvariants.completionEssentialImage F.val
  have he := LocalizingInvariants.stableClosure_completionEssentialImage F.val
    (multiSEndofunctor_map_isIdempotentCompletion r ι f hf).2.1
  have hm (z) : StableVertexClosure P z ↔ z ∈ P :=
    Iff.of_eq (congrArg (fun Q => z ∈ Q) he)
  let t := chosenPushoutCofiberRectangle L (IsStable.pushout_of_pullback_square L hL)
  have hA : squareVertex t.outerZeroTriangle.square 0 0 = squareVertex L 0 0 := by
    change squareVertex (pastingSquare t.diagram 2) 0 0 = _
    exact congrArg (fun D => squareVertex D 0 0) t.left_eq
  have hC : squareVertex t.outerZeroTriangle.square 1 0 = squareVertex L 0 1 := by
    change squareVertex (pastingSquare t.diagram 2) 0 1 = _
    exact congrArg (fun D => squareVertex D 0 1) t.left_eq
  have hB : squareVertex t.rightZeroTriangle.square 0 0 = squareVertex L 1 0 := by
    change squareVertex (pastingSquare t.diagram 2) 1 0 = _
    exact congrArg (fun D => squareVertex D 1 0) t.left_eq
  have hD : squareVertex t.rightZeroTriangle.square 1 0 = squareVertex L 1 1 := by
    change squareVertex (pastingSquare t.diagram 2) 1 1 = _
    exact congrArg (fun D => squareVertex D 1 1) t.left_eq
  have hE : StableVertexClosure P (squareVertex t.rightZeroTriangle.square 1 1) :=
    StableVertexClosure.of_cofiber t.rightZeroTriangle t.right_isCofiber
      (hB.symm ▸ (hm _).mpr h10) (hD.symm ▸ (hm _).mpr h11)
  have hE' : StableVertexClosure P (squareVertex t.outerZeroTriangle.square 1 1) := hE
  exact (hm _).mp (hA ▸ StableVertexClosure.of_fiber t.outerZeroTriangle
    (IsStable.pullback_of_pushout t.outerZeroTriangle t.outer_isCofiber)
      (hC.symm ▸ (hm _).mpr h01) hE')

/-- 概要：元の指定完備化射の同じ全多次数の本質像は閉じた安定頂点条件。
方針：同型・零対象・全押し出し・全引き戻しの閉性を束ねる。
規約：predicate は元の本質像そのもので、冪等完備閉包を取らない。
使われ方：K-B2-S1 の共通供給への本質像の実代入。 -/
def completionImageClosedPredicate (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : F2.Idempotent.IsIdempotentCompletion f.val) :
    ClosedStablePredicate (((multiSEndofunctor r).obj ι).obj Y) where
  predicate y := y ∈ LocalizingInvariants.completionEssentialImage
    (((multiSEndofunctor r).obj ι).map f).val
  of_iso := by
    rintro x y ⟨a, ⟨e⟩⟩ h
    exact ⟨a, ⟨e ≪≫ h⟩⟩
  zero_mem := by
    intro z hz
    let F := ((multiSEndofunctor r).obj ι).map f
    let : IsExactFunctor F.val := stableModelHom_exact F
    have he := LocalizingInvariants.stableClosure_completionEssentialImage F.val
      (multiSEndofunctor_map_isIdempotentCompletion r ι f hf).2.1
    exact he ▸ StableVertexClosure.of_zero hz
  pushout_mem := completionImage_pushout_mem r ι f hf
  pullback_mem := completionImage_pullback_mem r ι f hf

end SerrePositivity.KST.SConstruction.Cofinality
