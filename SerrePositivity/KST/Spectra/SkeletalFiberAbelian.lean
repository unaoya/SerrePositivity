module

public import SerrePositivity.KST.Spectra.SkeletalCoefficientDifferential

/-!
概要：骨格の写像空間の fiber の全正次数群は可換群。
方針：非退化単体上の二以上の次数の係数群との群同型で可換性を移す。
規約：fiber の基本群も含む。係数の基本群の可換性は仮定しない。
使われ方：Goerss–Jardine VIII §1。E_1 の加法的な係数表示。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K : SSet.{u}) (X : PointedSimplicialSet.{u}) [KanComplex X.right]

/-- 概要：各セルの係数の関数群は可換群。
方針：係数群の実際の次数が二以上であることを添字の整理で明示する。
規約：元の係数は Kan だけを仮定する。
使われ方：Goerss–Jardine I §7、VIII §1。fiber の基本群の可換性の移送。 -/
instance coefficientGroupCommGroup (n r : ℕ) : CommGroup (coefficientGroup K X n r) where
  __ := (inferInstance : Group (coefficientGroup K X n r))
  mul_comm a b := by
    apply funext
    intro s
    change a s * b s = b s * a s
    have h : ∀ (q : ℕ) (_ : 0 < q)
        (c d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X.right q X.basepoint), c * d = d * c := by
      intro q hq
      cases q with
      | zero => omega
      | succ q => exact mul_comm
    exact h _ (by omega) (a s) (b s)

lemma stageFiber_mul_comm (n r : ℕ)
    (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K X n).right r
      (UnbasedPointedMapping.stageFiber K X n).basepoint) : a * b = b * a := by
  apply (stageFiberCoefficientEquiv K X n r).injective
  simpa only [map_mul] using
    mul_comm (stageFiberCoefficientEquiv K X n r a) (stageFiberCoefficientEquiv K X n r b)

/-- 概要：骨格の fiber の基本群を含む全正次数群は可換。
方針：群構造を保ったまま係数表示の群同型の単射性で交換則を移す。
規約：既存の群構造の演算を変更しない。
使われ方：Goerss–Jardine VIII §1。塔の微分を加法群の射として扱う。 -/
instance stageFiberCommGroup (n r : ℕ) :
    CommGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K X n).right r
      (UnbasedPointedMapping.stageFiber K X n).basepoint) where
  __ := (inferInstance : Group (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup
    (UnbasedPointedMapping.stageFiber K X n).right r
      (UnbasedPointedMapping.stageFiber K X n).basepoint))
  mul_comm := stageFiber_mul_comm K X n r

end

end SerrePositivity.KST.Spectra.SkeletalCellAttachment
