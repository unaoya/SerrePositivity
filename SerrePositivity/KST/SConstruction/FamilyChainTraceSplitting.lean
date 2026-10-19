module
public import SerrePositivity.KST.SConstruction.FamilyHomotopyChains

/-! # 元の全 trace で指定する補正列の切断と末尾の実回収
概要：既存の全補正列を指定個数で切り、全区間と共有端点を保持する。
方針：元の列を帰納的に切断し、非空の trace の最後の面から終点の等号を得る。
規約：trace の区間を選び直さず、末尾の存在を入力仮定にしない。
使われ方：実比較複体の両側に共通する全末尾を元の補正列から取り出す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

/-- 非空の同じ全区間列は、その実終点も厳密に決める。 -/
lemma familyHomotopyChainTrace_target_eq {U E : SSet.{u}} {f g f' g' : U ⟶ E}
    (c : FamilyHomotopyChain f g) (d : FamilyHomotopyChain f' g')
    (ht : familyHomotopyChainTrace c = familyHomotopyChainTrace d)
    (hne : familyHomotopyChainTrace c ≠ []) : g = g' := by
  induction c generalizing f' g' with
  | nil => exact False.elim (hne rfl)
  | @cons f h g H tail ih =>
      cases d with
      | nil => cases ht
      | @cons f' h' g' K rest =>
          have he : H.h = K.h := (List.cons.inj ht).1
          have hr : familyHomotopyChainTrace tail = familyHomotopyChainTrace rest :=
            (List.cons.inj ht).2
          by_cases hn : familyHomotopyChainTrace tail = []
          · have hh : h = h' := by
              calc
                h = SSet.ι₁ ≫ H.h := H.h₁.symm
                _ = SSet.ι₁ ≫ K.h := congrArg (SSet.ι₁ ≫ ·) he
                _ = h' := K.h₁
            exact (familyHomotopyChain_eq_of_trace_nil tail hn).symm.trans
              (hh.trans (familyHomotopyChain_eq_of_trace_nil rest (hr.symm.trans hn)))
          · exact ih rest hr hn

/-- 元の補正列を切り、両側の全区間と同じ中間端点を保持するデータ。 -/
structure FamilyChainSplitData {U E : SSet.{u}} {f g : U ⟶ E}
    (c : FamilyHomotopyChain f g) (n : ℕ) where
  /-- 元の実中間族。 -/
  middle : U ⟶ E
  /-- 指定した先頭区間の全列。 -/
  before : FamilyHomotopyChain f middle
  /-- 残る元の全末尾。 -/
  after : FamilyHomotopyChain middle g
  /-- 先頭の trace は同じ元の take。 -/
  before_trace : familyHomotopyChainTrace before = (familyHomotopyChainTrace c).take n
  /-- 末尾の trace は同じ元の drop。 -/
  after_trace : familyHomotopyChainTrace after = (familyHomotopyChainTrace c).drop n

/-- 指定した長さで元の実列を切断する。 -/
def familyChainSplit {U E : SSet.{u}} {f g : U ⟶ E}
    (c : FamilyHomotopyChain f g) (n : ℕ) : FamilyChainSplitData c n := by
  induction n generalizing f g with
  | zero => exact ⟨f, .nil f, c, rfl, rfl⟩
  | succ n ih =>
      cases c with
      | nil f => exact ⟨f, .nil f, .nil f, rfl, rfl⟩
      | cons H tail =>
          let s := ih tail
          exact ⟨s.middle, .cons H s.before, s.after,
            congrArg (H.h :: ·) s.before_trace, s.after_trace⟩

/-- 既存の全列から、同じ非空先頭 trace を持つ別の辺路の後の実末尾を回収する。 -/
def familyChainPrefixTail {U E : SSet.{u}} {f g a b : U ⟶ E}
    (c : FamilyHomotopyChain f g) (initial : FamilyHomotopyChain a b)
    (ht : (familyHomotopyChainTrace c).take (familyHomotopyChainTrace initial).length =
      familyHomotopyChainTrace initial) (hne : familyHomotopyChainTrace initial ≠ []) :
    FamilyHomotopyChain b g := by
  let s := familyChainSplit c (familyHomotopyChainTrace initial).length
  have he : s.middle = b := familyHomotopyChainTrace_target_eq s.before initial
    (s.before_trace.trans ht) (fun h => hne ((s.before_trace.trans ht).symm.trans h))
  exact familyHomotopyChainSourceTransport s.after he.symm

/-- 回収した実末尾は元の drop の全区間を同じ順序で持つ。 -/
lemma familyChainPrefixTail_trace {U E : SSet.{u}} {f g a b : U ⟶ E}
    (c : FamilyHomotopyChain f g) (initial : FamilyHomotopyChain a b)
    (ht : (familyHomotopyChainTrace c).take (familyHomotopyChainTrace initial).length =
      familyHomotopyChainTrace initial) (hne : familyHomotopyChainTrace initial ≠ []) :
    familyHomotopyChainTrace (familyChainPrefixTail c initial ht hne) =
      (familyHomotopyChainTrace c).drop (familyHomotopyChainTrace initial).length := by
  rw [familyChainPrefixTail, familyHomotopyChainSourceTransport_trace]
  exact (familyChainSplit c (familyHomotopyChainTrace initial).length).after_trace

end SerrePositivity.KST.SConstruction
