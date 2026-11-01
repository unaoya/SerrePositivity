module
public import SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity
public import SerrePositivity.InfinityCategories.F1.Coherent.HomIntervalVertices
public import SerrePositivity.InfinityCategories.Core.UniverseInitialTerminal
public import SerrePositivity.InfinityCategories.Core.FullSubcomplexFibration
public import SerrePositivity.KST.LocalizingInvariants.ZeroMaps
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FullSubcomplexMapping
public import SerrePositivity.InfinityCategories.F1.Cocartesian.RelativeUnitHom

/-!
概要：全零完全関手の固定端点区間 Hom では、自己比較の射の類が一意となる。
方針：完全関手圏の終対象全成分を coherent 区間 Hom 比較へ充満忠実に写す。
規約：元の完全関手・元の区間を保持。自然な収縮を追加入力にしない。
使われ方：恒等実右面の上下比較の共有対角を同じ全比較へ合わせる。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet InfinityCategories LocalizingInvariants
open scoped Simplicial
local instance zeroIntervalStableHomKan : ∀ X Y : StableQCat.{u}, KanComplex (SimplicialCategory.sHom X Y) :=
  fun X Y => stableQCat_sHom_kanComplex X Y
variable (A B : StableCategory.{u})
local instance zeroIntervalLiftedStableHomKan : KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj
    (SimplicialCategory.sHom (C := StableQCat.{u}) A B)) := by
  letI : KanComplex (SimplicialCategory.sHom (C := StableQCat.{u}) A B) :=
    stableQCat_sHom_kanComplex A B
  exact kanComplex_uliftFunctor_obj _

private abbrev zeroIntervalComponent : SSet.{u + 1} :=
  fullSubcomplexOnVertices ((SSet.uliftFunctor.{u + 1, u}).obj
    (SimplicialCategory.sHom (C := StableQCat.{u}) A B))
    (fun x => IsTerminalVertex x.down.val)

private def zeroIntervalComponentIso
    (h : ∃ x : (exactFunctors A B : SSet.{u}) _⦋0⦌, IsTerminalVertex x) :
    (SSet.uliftFunctor.{u + 1, u}).obj
        (terminalVertices (exactFunctors A B : SSet.{u}) : SSet.{u}) ≅
      zeroIntervalComponent A B := by
  let X := (terminalVertices (exactFunctors A B : SSet.{u}) : SSet.{u})
  have hc : IsContractibleKan X := terminalVertices_isContractibleKan h
  letI : KanComplex X := hc.kanComplex
  let j : X ⟶ SimplicialCategory.sHom (C := StableQCat.{u}) A B :=
    quasicategoryCoreLift (terminalVertices (exactFunctors A B : SSet.{u})).ι
      (fun s => by
        have hs : IsInvertibleEdge (edgeOfSimplex s) :=
          IsGroupoid.all_isIso (C := hoFunctor.obj X) _
        exact (isInvertibleEdge_congr (by rfl)).mp
          (hs.map (terminalVertices (exactFunctors A B : SSet.{u})).ι))
  refine {
    hom := fullSubcomplexLift _ ((SSet.uliftFunctor.{u + 1, u}).map j)
      (fun x => fullSubcomplexOnVertices_vertex x.down)
    inv := {
      app n := ↾fun x => ULift.up ⟨x.val.down.val, fun α => x.property α⟩
      naturality n m α := by
        apply ConcreteCategory.hom_ext
        intro x
        apply ULift.ext
        apply Subtype.ext
        rfl }
    hom_inv_id := ?_
    inv_hom_id := ?_ }
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    apply Subtype.ext
    rfl
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    apply ULift.ext
    apply Subtype.ext
    rfl

private lemma zeroIntervalComponent_contractible
    (h : ∃ x : (exactFunctors A B : SSet.{u}) _⦋0⦌, IsTerminalVertex x) :
    IsContractibleKan (zeroIntervalComponent A B) := by
  apply isContractibleKan_of_iso (zeroIntervalComponentIso A B h)
  have hc := terminalVertices_isContractibleKan h
  apply isContractibleKan_of_nonempty_of_all_terminal
  · exact ⟨ULift.up (Classical.choice hc.nonempty)⟩
  · intro x
    exact (isTerminalVertex_iff_ulift x.down).mp (hc.isTerminalVertex x.down)

/-- 概要：元全零完全関手の同じ固定端点区間 Hom の自己射の類は一意。
方針：元終対象成分の可縮性と全 Hom 比較の充満忠実性を使う。
規約：両端固定の全自己比較。使われ方：上下比較の対角の類の一致への還元。 -/
lemma stableZeroInterval_hom_ext (F : ExactMap A B)
    (hF : ∀ x, IsZeroVertex (F.hom.app (Opposite.op ⦋0⦌) x))
    (f g : SSet.HomotopyCategory.mk (intervalMappingVertexOfEdge (stableArrow F)) ⟶
      SSet.HomotopyCategory.mk (intervalMappingVertexOfEdge (stableArrow F))) : f = g := by
  have ht : IsTerminalVertex (exactFunctorVertexEquiv A B F) := by
    apply (isFullyFaithful_fullSubcomplexOnVertices_ι _ _).reflects_isTerminalVertex
    change IsTerminalVertex (functorVertex F.hom)
    exact isTerminalVertex_functorVertex_of_pointwise _ (fun x => (hF x).2)
  let z : (zeroIntervalComponent A B) _⦋0⦌ := fullSubcomplexVertexEquiv _
    ⟨ULift.up (SimplicialCategory.homEquiv' (C := StableQCat.{u}) A B F), ht⟩
  let M : zeroIntervalComponent A B ⟶ intervalMappingSpace (stableVertex A) (stableVertex B) :=
    (fullSubcomplexOnVertices ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (C := StableQCat.{u}) A B))
      (fun x => IsTerminalVertex x.down.val)).ι ≫
        coherentHomIntervalComparison (C := StableQCat.{u}) A B
  have hc := zeroIntervalComponent_contractible A B ⟨_, ht⟩
  letI : KanComplex (zeroIntervalComponent A B) := hc.kanComplex
  have hM : IsFullyFaithful M := (isFullyFaithful_fullSubcomplexOnVertices_ι _ _).comp
    (coherentHomIntervalComparison_isQCatEquivalence (C := StableQCat.{u}) A B).isFullyFaithful
  have hz : M.app (Opposite.op ⦋0⦌) z = intervalMappingVertexOfEdge (stableArrow F) := by
    change (coherentHomIntervalComparison (C := StableQCat.{u}) A B).app _
      (ULift.up (SimplicialCategory.homEquiv' (C := StableQCat.{u}) A B F)) = _
    have he := coherentHomIntervalComparison_vertex (C := StableQCat.{u})
      (SimplicialCategory.homEquiv' (C := StableQCat.{u}) A B F)
    exact he.trans (congrArg
      (fun K : (A : StableQCat.{u}) ⟶ (B : StableQCat.{u}) =>
        intervalMappingVertexOfEdge (coherentNerveEdge (C := StableQCat.{u}) K))
      (Equiv.symm_apply_apply
        (SimplicialCategory.homEquiv' (C := StableQCat.{u}) A B) F))
  have hs : Subsingleton (SSet.HomotopyCategory.mk (M.app (Opposite.op ⦋0⦌) z) ⟶
      SSet.HomotopyCategory.mk (M.app (Opposite.op ⦋0⦌) z)) := by
    constructor
    intro a b
    have hb := IsFullyFaithful.homotopyCategoryMap_bijective hM z z
    obtain ⟨a', ha⟩ := hb.2 a
    obtain ⟨b', hb⟩ := hb.2 b
    exact ha.symm.trans ((congrArg ((hoFunctor.map M).toFunctor.map)
      ((hc.isTerminalVertex z).isTerminalHo.hom_ext a' b')).trans hb)
  rw [hz] at hs
  exact hs.elim f g
end SerrePositivity.KST.SConstruction
