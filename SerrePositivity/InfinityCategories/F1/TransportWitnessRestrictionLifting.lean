module

public import SerrePositivity.InfinityCategories.F1.TransportSquareRepresentationRestriction
public import SerrePositivity.InfinityCategories.F1.TransportWitnessRestrictionInner
public import SerrePositivity.InfinityCategories.F1.RelativeHomEquivalenceRestriction

/-!
概要：周囲の四角形の充填から表現空間の相対充填を得る。
方針：全頂点を被覆する底変換で各頂点の表現条件を反映する。
規約：幾何学的な同値条件と全単射に対する持ち上げの形式的帰結を分ける。
使われ方：Kerodon Lemma 5.6.8.10 (2)、境界固定延長。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

local instance {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B) :
    LeftFibration (pullback.snd p g) :=
  ⟨leftFibrations.pullback_snd p g (LeftFibration.mem (p := p))⟩

/-- 概要：全頂点を被覆する底への制限で表現空間の頂点条件を反映する。
方針：頂点の四角形を回収し、制限の頂点公式と fiber 判定を使う。
規約：底変換に単射性を要求しない。
使われ方：周囲の空間で作った持ち上げの各頂点の検査。 -/
lemma isTransportWitnessVertex_of_restriction {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B)
    (hg : Function.Surjective (g.app (Opposite.op ⦋0⦌)))
    (v : (transportSquareSpace p) _⦋0⦌)
    (hv : IsTransportWitnessVertex (pullback.snd p g)
      ((transportSquareRestriction p g).app _ v)) : IsTransportWitnessVertex p v := by
  let S := transportSquareOfVertex p v
  have hS : transportSquareVertex S = v := transportSquareVertex_ofVertex p v
  rw [← hS, transportSquareRestriction_vertex] at hv
  have hr := (isTransportWitnessVertex_iff_isRepresentation _ _).1 hv
  have h := (S.isRepresentation_iff_restrict_of_vertexSurjective g hg).2 hr
  rw [← hS]
  exact (isTransportWitnessVertex_iff_isRepresentation p S).2 h

/-- 概要：四角形の制限の持ち上げ性は全頂点を被覆する底で表現空間へ制限できる。
方針：周囲で充填し、下側の表現条件を各頂点で反映する。
規約：i は任意の射で、単射性も次元の制限も不要。
使われ方：表現空間の境界充填と任意のパラメーター上の相対延長。 -/
lemma hasLiftingProperty_transportWitnessRestriction_of_square
    {E B D T U : SSet.{u + 1}} (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B)
    (hg : Function.Surjective (g.app (Opposite.op ⦋0⦌))) (i : T ⟶ U)
    [HasLiftingProperty i (transportSquareRestriction p g)] :
    HasLiftingProperty i (transportWitnessRestriction p g) := by
  constructor
  intro a b sq
  let sq' : CommSq (a ≫ transportWitnessSpaceι p) i (transportSquareRestriction p g)
      (b ≫ transportWitnessSpaceι (pullback.snd p g)) := ⟨by
    rw [Category.assoc, ← transportWitnessRestriction_ι, ← Category.assoc,
      sq.w, Category.assoc]⟩
  have hv : ∀ v : U _⦋0⦌, IsTransportWitnessVertex p (sq'.lift.app _ v) := by
    intro v
    apply isTransportWitnessVertex_of_restriction p g hg
    have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) v) sq'.fac_right
    change (transportSquareRestriction p g).app _ (sq'.lift.app _ v) = (b.app _ v).val at h
    rw [h]
    exact fullSubcomplexOnVertices_vertex (b.app _ v)
  let L := fullSubcomplexLift (IsTransportWitnessVertex p) sq'.lift hv
  have hL : L ≫ transportWitnessSpaceι p = sq'.lift := fullSubcomplexLift_ι _ _ _
  refine CommSq.HasLift.mk' { l := L, fac_left := ?_, fac_right := ?_ }
  · apply (cancel_mono (transportWitnessSpaceι p)).1
    rw [Category.assoc, hL]
    exact sq'.fac_left
  · apply (cancel_mono (transportWitnessSpaceι (pullback.snd p g))).1
    rw [Category.assoc, transportWitnessRestriction_ι, ← Category.assoc, hL]
    exact sq'.fac_right

/-- 概要：周囲の四角形の全単射の充填は表現空間の全単射の充填を与える。
方針：頂点全射性を使う充填の制限を全単射に適用する。
規約：周囲の trivial Kan 性は明示的な補助入力。
使われ方：Kerodon Lemma 5.6.8.10 (2) の形式的部分。 -/
lemma transportWitnessRestriction_trivialKanFibration_of_square
    {E B D : SSet.{u + 1}} (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B)
    (hg : Function.Surjective (g.app (Opposite.op ⦋0⦌)))
    (hq : TrivialKanFibration (transportSquareRestriction p g)) :
    TrivialKanFibration (transportWitnessRestriction p g) := by
  constructor
  intro T U i hi
  have := hq.mem i hi
  exact hasLiftingProperty_transportWitnessRestriction_of_square p g hg i

/-- 概要：底側と全空間側の単射な前合成同値は四角形の制限の全単射充填を与える。
方針：分類図式の制限と相対内部 Hom の trivial Kan 性を組み合わせる。
規約：引き戻しの前合成同値は幾何学的な補題で供給する明示的な条件。
使われ方：Kerodon Lemma 5.6.8.10 (2)、全空間の逆像の同値性を適用する箇所。 -/
lemma transportSquareRestriction_trivialKanFibration_of_precompositionEquivalences
    {E B D : SSet.{u + 1}} (p : E ⟶ B) (g : D ⟶ B) [Mono g]
    (hg : IsPrecompositionEquivalence g)
    (hE : IsPrecompositionEquivalence (pullback.fst p g)) :
    TrivialKanFibration (transportSquareRestriction p g) := by
  let r := Functor.PullbackObjObj.ofHasPullback internalHom
    (pullback.fst p g) pointedSpaceProjection
  have := hg.trivialKanFibration_pre SpaceInfinity.{u}
  have := trivialKanFibration_relativeHom_of_precompositionEquivalence
    (pullback.fst p g) hE pointedSpaceProjection r
  constructor
  intro T U i hi
  have := TrivialKanFibration.mem (p := (pre g).app SpaceInfinity.{u}) i hi
  have := TrivialKanFibration.mem (p := r.π) i hi
  exact hasLiftingProperty_transportSquareRestriction p g i r

end SerrePositivity.InfinityCategories
