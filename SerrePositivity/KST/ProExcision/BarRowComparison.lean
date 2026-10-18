module
public import SerrePositivity.KST.ProExcision.CoefficientBisimplicialBar
public import SerrePositivity.KST.ProExcision.TuplePrefix

/-!
# Prop A.1 の各行の比較と prefix 作用

概要：二重 bar の比較を同じ有限積上の prefix 作用へ移す。
方針：始点とラベルの座標と半直積の二つの成分を使う。
規約：KST Proposition A.1 の逆順の語の座標。
使われ方：群状作用の有限合成による各行の局所化同値性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite MonoidalCategory
open SerrePositivity.KST.Comparison
open scoped Simplicial
variable {G H : SimplicialObject MonCat.{u}}

/-- 概要：係数作用 bar の各行を G^r×H^r の順で表示する。
方針：始点の H 座標と G のラベル列の順序を交換する。
規約：KST Proposition A.1。使われ方：作用の族の定義域との同定。 -/
def coefficientRowProductIso (A : SimplicialMonoidAction G H) (r : ℕ) :
    (coefficientBisimplicialBar A).flip.obj (op ⦋r⦌) ≅
      monoidTupleSpace G r ⊗ monoidSpace (tupleMonoid H r) :=
  coefficientBisimplicialBarRowIso A r ≪≫ (β_ _ _) ≪≫
    tensorIso (Iso.refl _) (tupleMonoidSpaceIso H r).symm

/-- 概要：半直積の有限列の台を二つの有限列の直積へ送る。
方針：各元の base と fiber を取り出す。
規約：モノイドの同型とは主張しない。使われ方：KST Proposition A.1 の終域の座標。 -/
def tupleActionProductUnderlyingIso (A : SimplicialMonoidAction G H) (r : ℕ) :
    monoidTupleSpace (simplicialActionProduct A) r ≅
      monoidTupleSpace G r ⊗ monoidSpace (tupleMonoid H r) where
  hom := { app n := ↾fun h ↦ (fun j ↦ (h j).base, fun j ↦ (h j).fiber) }
  inv := { app n := ↾fun p j ↦ ⟨p.1 j, p.2 j⟩ }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- 概要：半直積 bar の各行を G^r×H^r として表示する。
方針：Segal 座標と半直積の成分の同型を合成する。
規約：KST Proposition A.1。使われ方：作用 bar の行と同じ積上で比較する。 -/
def semidirectBarRowProductIso (A : SimplicialMonoidAction G H) (r : ℕ) :
    (bisimplicialBar (simplicialActionProduct A)).flip.obj (op ⦋r⦌) ≅
      monoidTupleSpace G r ⊗ monoidSpace (tupleMonoid H r) :=
  monoidBarRowIso (simplicialActionProduct A) r ≪≫ tupleActionProductUnderlyingIso A r

/-- 概要：二重 bar 比較の第 r 行。
方針：二つの単体方向を交換して第 r 成分を取る。
規約：KST Proposition A.1。使われ方：行ごとの局所化同値性の命題。 -/
abbrev coefficientBarRowComparison (A : SimplicialMonoidAction G H) (r : ℕ) :=
  ((flipFunctor _ _ _).map (coefficientBisimplicialBarComparison A)).app (op ⦋r⦌)

/-- 概要：各行の比較は積座標で指定座標の作用の有限合成となる。
方針：始点から j+1 までの作用圏の射の条件と prefix の積の計算を使う。
規約：KST Proposition A.1 の逆順の語の座標。
使われ方：群状な G の作用の族から行の同値性を得る。 -/
theorem coefficientBarRowComparison_eq_sweep (A : SimplicialMonoidAction G H) (r : ℕ) :
    (coefficientRowProductIso A r).hom ≫ tupleActionSweep A r (le_refl r) =
      coefficientBarRowComparison A r ≫ (semidirectBarRowProductIso A r).hom := by
  apply NatTrans.ext
  funext n
  let Ac := constantSimplicialMonoidAction (G.obj n) (H.obj n) (A.action n)
  letI : MulAction (G.obj n) ((nerve (SingleObj (H.obj n))) _⦋r⦌) :=
    (barSetAction Ac).actionStructure (op ⦋r⦌)
  apply ConcreteCategory.hom_ext
  intro p
  change (nerve (ActionObject (G.obj n)
    ((nerve (SingleObj (H.obj n))) _⦋r⦌))) _⦋r⦌ at p
  apply Prod.ext
  · exact tupleActionSweep_base A r (le_refl r) n _ _
  · funext j
    change Fin r at j
    change ((tupleActionSweep A r (le_refl r)).app n
      ((actionNerveCoordinates p).2, monoidWordLabels (H.obj n) (p.obj 0).val)).2 j =
        monoidWordLabels (H.obj n) (p.obj ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩).val j
    rw [tupleActionSweep_fiber]
    have hj : min r (j.val + 1) = j.val + 1 := min_eq_right (by omega)
    simp only [hj]
    have hp := (p.map' 0 (j.val + 1) (Nat.zero_le _) (Nat.succ_le_of_lt j.isLt)).property
    have hh := congrArg (fun b : (nerve (SingleObj (H.obj n))) _⦋r⦌ ↦
      monoidWordLabels (H.obj n) b j) hp
    change A.action n (p.map' 0 (j.val + 1) (Nat.zero_le _) (Nat.succ_le_of_lt j.isLt)).val
      (monoidWordLabels (H.obj n) (p.obj 0).val j) = _ at hh
    have hl := monoidNerve_prefix_eq (MonCat.of (G.obj n))
      (p ⋙ actionCategoryProjection) (j.val + 1) (Nat.succ_le_of_lt j.isLt)
    change (p.map' 0 (j.val + 1) (Nat.zero_le _) (Nat.succ_le_of_lt j.isLt)).val =
      tuplePrefixProduct (actionNerveCoordinates p).2 (j.val + 1) (Nat.succ_le_of_lt j.isLt) at hl
    rw [hl] at hh
    exact hh

/-- 概要：群状な G の作用に対する各行の比較は局所化で可逆。
方針：積座標での有限合成との等式と各段の可逆性を使う。
規約：KST Proposition A.1 の各行の同値性の局所化模型。
使われ方：対角の比較を局所化で同型とする入力。 -/
theorem coefficientBarRowComparison_localized_isIso (A : SimplicialMonoidAction G H)
    (hG : SimplicialMonoid.IsGrouplike G) (r : ℕ) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (coefficientBarRowComparison A r)) := by
  let Q := SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ
  haveI := tupleActionSweep_localized_isIso A hG r (le_refl r)
  have hn := congrArg Q.map (coefficientBarRowComparison_eq_sweep A r)
  simp only [CategoryTheory.Functor.map_comp] at hn
  have hc : IsIso (Q.map (coefficientBarRowComparison A r) ≫
      Q.map (semidirectBarRowProductIso A r).hom) :=
    hn ▸ inferInstanceAs (IsIso (Q.map (coefficientRowProductIso A r).hom ≫
      Q.map (tupleActionSweep A r (le_refl r))))
  exact (isIso_comp_right_iff _ _).mp hc

end SerrePositivity.KST.ProExcision
