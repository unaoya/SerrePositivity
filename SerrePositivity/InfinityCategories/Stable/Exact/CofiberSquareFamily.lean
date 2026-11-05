module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberInputFamily

/-!
概要：元の矢印族を保つ普遍 cofiber 四角形の全単体族。
方針：零枝つき span の族に普遍余錐を coherent に選び、正方形へ戻す。
規約：頂点ごとの cofiber の選択だけにしない。使われ方：差の実 ∞ 関手。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberFamily
end SerrePositivity.KST.LocalizingInvariants.CofiberFamily
namespace SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily
open SerrePositivity.KST.LocalizingInvariants.CofiberFamily

variable (X : SSet.{u}) [Quasicategory X] [IsStable X]
  {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)

def cocones : A ⟶ colimitCocones (horn 2 0 : SSet.{u}) X :=
  Classical.choose (exists_colimitCoconeFamily (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.span X a) (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.span_hasColimit X a))

lemma cocones_projection : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cocones X a ≫ colimitCoconeProjection (horn 2 0 : SSet.{u}) X =
    _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.span X a :=
  Classical.choose_spec (exists_colimitCoconeFamily (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.span X a) (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.span_hasColimit X a))

def squares : A ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X :=
  _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cocones X a ≫ (relativeInitialVertices (coconeRestriction (horn 2 0 : SSet.{u}) X)).ι ≫
    (pre spanCoconeSquareIso.inv).app X

lemma squares_cocones : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares X a ≫ (pre spanCoconeSquareIso.hom).app X =
    _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cocones X a ≫ (relativeInitialVertices (coconeRestriction (horn 2 0 : SSet.{u}) X)).ι := by
  simp only [_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares, Category.assoc, ← NatTrans.comp_app, ← pre_map, Iso.hom_inv_id,
    pre_id, NatTrans.id_app, Category.comp_id]

lemma squares_span : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares X a ≫ (pre spanSquareBoundary).app X = _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.span X a := by
  rw [_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares]
  simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map]
  have hi : spanSquareBoundary ≫ spanCoconeSquareIso.inv =
      joinInl (horn 2 0 : SSet.{u}) Δ[0] := by
    simp only [spanSquareBoundary, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hi]
  exact _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cocones_projection X a

lemma squares_bottom : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares X a ≫ (pre squareBottomEdge).app X = a := by
  have h := congrArg (fun f ↦ f ≫ (pre horn₂₀.ι₀₁).app X) (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares_span X a)
  rw [_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.span_left] at h
  simpa only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
    spanSquareBoundary_bottomEdge] using h

lemma squares_left : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares X a ≫ (pre squareLeftEdge).app X = _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroArrow X a := by
  have h := congrArg (fun f ↦ f ≫ (pre horn₂₀.ι₀₂).app X) (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares_span X a)
  rw [_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.span_right] at h
  simpa only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
    spanSquareBoundary_leftEdge] using h

def squareAt (x : A _⦋0⦌) : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X :=
  squareDiagram ((_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares X a).app _ x)

lemma squareAt_isPushout (x : A _⦋0⦌) : IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt X a x) := by
  apply (isColimitCone_iff_initialBoundaryLifting (pushoutCocone (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt X a x))).2
  have hv := fullSubcomplexOnVertices_vertex ((_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cocones X a).app (Opposite.op ⦋0⦌) x)
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares_cocones X a) (Opposite.op ⦋0⦌)) x
  change ((pre spanCoconeSquareIso.hom).app X).app _ ((_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares X a).app _ x) =
    ((_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cocones X a).app _ x).val at he
  have hs : functorVertex (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt X a x) = (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares X a).app _ x :=
    (functorVertexEquiv _ _).apply_symm_apply _
  change InitialBoundaryLifting _ (functorVertex (spanCoconeSquareIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt X a x))
  change InitialBoundaryLifting _ (((pre spanCoconeSquareIso.hom).app X).app _
    (functorVertex (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt X a x)))
  rw [hs, he]
  exact hv

lemma squareAt_zero (x : A _⦋0⦌) : IsZeroVertex (squareVertex (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt X a x) 0 1) := by
  have h := congrArg (fun f ↦ f ≫ evaluateFunctorAt
    (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares_left X a)
  rw [Category.assoc, stable_pre_evaluateFunctorAt] at h
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app h (Opposite.op ⦋0⦌)) x
  have hz : IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroArrow X a ≫ evaluateFunctorAt
      (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app (Opposite.op ⦋0⦌) x) :=
    fullSubcomplexOnVertices_vertex
      ((a ≫ evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≫
        _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroArrowSection X).app _ x)
  rw [← he] at hz
  have hs : functorVertex (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt X a x) = (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares X a).app _ x :=
    (functorVertexEquiv _ _).apply_symm_apply _
  change IsZeroVertex ((evaluateFunctorAt _).app (Opposite.op ⦋0⦌)
    ((_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares X a).app _ x)) at hz
  rw [← hs, evaluateFunctorAt_functorVertex] at hz
  exact hz

set_option maxHeartbeats 800000 in
-- 選択した普遍余錐の curry 表示と元の全族の底辺の表示を照合する。
lemma squareAt_bottom (x : A _⦋0⦌) : squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt X a x =
    (functorVertexEquiv Δ[1] X).symm (a.app _ x) := by
  apply (functorVertexEquiv Δ[1] X).injective
  rw [(functorVertexEquiv Δ[1] X).apply_symm_apply]
  have hs : functorVertex (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt X a x) = (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares X a).app _ x :=
    (functorVertexEquiv _ _).apply_symm_apply _
  change ((pre squareBottomEdge).app X).app _ (functorVertex (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt X a x)) = _
  rw [hs]
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares_bottom X a) (Opposite.op ⦋0⦌)) x
  change ((pre squareBottomEdge).app X).app (Opposite.op ⦋0⦌)
    ((_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares X a).app (Opposite.op ⦋0⦌) x) = a.app (Opposite.op ⦋0⦌) x at he
  exact he

def cofiberSquareAt (x : A _⦋0⦌) :
    CofiberSquare (edgeOfSimplex (intervalFunctorVertexEdge (a.app _ x))) where
  square := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt X a x
  zero_corner := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt_zero X a x
  bottom_edge := by
    change squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt X a x = SSet.yonedaEquiv.symm
      (SSet.yonedaEquiv ((functorVertexEquiv Δ[1] X).symm (a.app _ x)))
    rw [Equiv.symm_apply_apply]
    exact _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt_bottom X a x
  isPushout := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt_isPushout X a x

/-- 元の任意の矢印族の cofiber を与える、全単体上の実関手。 -/
def cofiber : A ⟶ X := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares X a ≫ evaluateFunctorAt
  (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2), SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))

lemma cofiber_vertex (x : A _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber X a).app _ x = (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiberSquareAt X a x).cofiber := by
  have hs : functorVertex (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt X a x) = (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares X a).app _ x :=
    (functorVertexEquiv _ _).apply_symm_apply _
  change (evaluateFunctorAt _).app (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares X a).app _ x) = _
  rw [← hs, evaluateFunctorAt_functorVertex]
  rfl

end SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cocones (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.cocones := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cocones

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.cocones_projection := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cocones_projection

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.cofiber := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiberSquareAt (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.cofiberSquareAt := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiberSquareAt

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.cofiber_vertex := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber_vertex

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.squareAt := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.squareAt_bottom := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt_bottom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.squareAt_isPushout := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt_isPushout

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.squareAt_zero := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt_zero

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.squares := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.squares_bottom := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares_bottom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.squares_cocones := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares_cocones

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.squares_left := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.squares_span := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares_span

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.cocones._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cocones._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.cocones._proof_2 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cocones._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.cocones.congr_simp := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cocones.congr_simp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.cofiber._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.cofiberSquareAt._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiberSquareAt._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.cofiberSquareAt._proof_2 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiberSquareAt._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.squares.congr_simp := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares.congr_simp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.squares.eq_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares.eq_1
