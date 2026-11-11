module

public import SerrePositivity.KST.Comparison.BarFundamentalRepresentatives
public import SerrePositivity.KST.Comparison.GrouplikeComparison
public import SerrePositivity.KST.Comparison.MonoidComponentsFunctor
public import SerrePositivity.KST.Comparison.StableGLComponents

/-!
# 群状モノイドの成分群と分類空間の基本群

概要：群状モノイドの実際の成分群を分類空間の基本群と乗法的に同定する。
方針：標準写像の成分上の全単射を辺の反乗法性と合わせ、逆元を前合成する。
規約：KST Lemma 2.13 の i=1。逆元の前合成は SingleObj の合成の向きによる。
使われ方：安定一般線形群と BĜL の基本群の群同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite SSet
open scoped Simplicial
open SerrePositivity.SimplicialModel

/--
概要：標準群完備化写像と円の成分比較による基本群への写像。
方針：連結成分の誘導写像を K-L9 の球面の代表による比較へ合成する。
規約：正向きの辺を使うので反乗法的。
使われ方：基本群の乗法との整合の証明。
-/
def monoidBarFundamentalClass (M : SimplicialObject MonCat.{u}) :
    π₀ (monoidSpace M) → _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (monoidBarKanPointed M).right 0
      (monoidBarKanPointed M).basepoint :=
  fun a => Spectra.SphereSimplex.componentClass (monoidBarKanPointed M) 0
    (mapπ₀ (monoidGroupCompletionMap M) a)

/--
概要：成分から基本群への標準写像の零次代表での計算。
方針：写像空間の頂点を表す円の写像と nerve の辺の代表の一致を使う。
規約：具体的な境界定数単体を保持する。
使われ方：単位・積の代表による検証。
-/
theorem monoidBarFundamentalClass_mk (M : SimplicialObject MonCat.{u})
    (a : M.obj (op ⦋0⦌)) :
    monoidBarFundamentalClass M (π₀.mk a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (monoidBarVertexLoop M a) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk
    (Spectra.SphereSimplex.equiv (monoidBarKanPointed M) 1
      (Spectra.PointedMapping.familyMap _ _ ((monoidGroupCompletionMap M).app _ a))) = _
  rw [groupCompletionVertex_eq_barLoop]

/--
概要：群状モノイドの成分から基本群への標準写像は全単射。
方針：群完備化の局所化可逆性から π₀ の全単射を得て、円の成分比較と合成する。
規約：元のモノイドの Kan 性を要求しない。
使われ方：乗法的同型の全単射性。
-/
theorem monoidBarFundamentalClass_bijective (M : SimplicialObject MonCat.{u})
    (hM : SimplicialMonoid.IsGrouplike M) : Function.Bijective (monoidBarFundamentalClass M) :=
  (Spectra.SphereSimplex.componentClass_bijective (monoidBarKanPointed M) 0).comp
    (PiZeroLocalization.piZero_bijective _ (monoidGroupCompletionMap_localized_isIso M hM))

/--
概要：成分から基本群への正向きの標準写像は反乗法的。
方針：零次代表へ下ろし、nerve の二単体の積の充填を後合成する。
規約：成分の積は実際の零次の積から誘導する。
使われ方：逆元の前合成による群同型。
-/
theorem monoidBarFundamentalClass_mul (M : SimplicialObject MonCat.{u})
    (a b : SimplicialMonoid.componentsObject M) :
    monoidBarFundamentalClass M (b * a) =
      monoidBarFundamentalClass M a * monoidBarFundamentalClass M b := by
  let : Monoid ((monoidSpace M).obj (op ⦋0⦌)) :=
    inferInstanceAs (Monoid (M.obj (op ⦋0⦌)))
  induction a using π₀.rec with | mk a => ?_
  induction b using π₀.rec with | mk b => ?_
  change monoidBarFundamentalClass M (π₀.mk (b * a)) = _
  rw [monoidBarFundamentalClass_mk, monoidBarFundamentalClass_mk,
    monoidBarFundamentalClass_mk]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapMulStruct (monoidVertexNerveKanMap M) (monoidVertexNerveKanMap_point M)
      (monoidNerveLoopMulStruct (M.obj (op ⦋0⦌)) a b))).symm

/--
概要：群状モノイドの誘導成分群と分類空間の基本群の乗法同値。
方針：正向きの辺の反乗法性へ逆元を前合成し、標準比較の全単射性を使う。
規約：Segal 1974 Proposition 1.5、KST Lemma 2.13 の i=1。
使われ方：一般線形群との群としての比較。
-/
def monoidBarFundamentalMulEquiv (M : SimplicialObject MonCat.{u})
    (hM : SimplicialMonoid.IsGrouplike M) :
    letI := SimplicialMonoid.componentsGroup M hM
    π₀ (monoidSpace M) ≃* _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (monoidBarKanPointed M).right 0
      (monoidBarKanPointed M).basepoint := by
  letI := SimplicialMonoid.componentsGroup M hM
  refine
    { Equiv.ofBijective (fun a : π₀ (monoidSpace M) => monoidBarFundamentalClass M a⁻¹)
        ((monoidBarFundamentalClass_bijective M hM).comp inv_involutive.bijective) with
      map_mul' := fun a b => ?_ }
  change monoidBarFundamentalClass M (a * b)⁻¹ = _
  rw [mul_inv_rev]
  let ia : π₀ (monoidSpace M) := a⁻¹
  let ib : π₀ (monoidSpace M) := b⁻¹
  exact monoidBarFundamentalClass_mul M ia ib

/--
概要：安定 GL(π₀A) と BĜL(A) の基本群の乗法同値。
方針：誘導乗法を保つ安定成分の同型と群状モノイドの基本群の比較を合成する。
規約：KST Lemma 2.13 の i=1。逆元の辺を使う群同型。
使われ方：plus による基本群の商と K₁ への接続。
-/
def stableHatGLBarFundamentalMulEquiv (A : SimplicialObject RingCat.{u}) :
    stableGeneralLinear (π₀ (ringSpace A)) ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (monoidBarKanPointed (stableHatGL A)).right 0
        (monoidBarKanPointed (stableHatGL A)).basepoint :=
  (Iso.monCatIsoToMulEquiv (stableHatGLComponentsIso A)).symm.trans
    (monoidBarFundamentalMulEquiv (stableHatGL A) (stableHatGL_isGrouplike A))

end SerrePositivity.KST.Comparison
