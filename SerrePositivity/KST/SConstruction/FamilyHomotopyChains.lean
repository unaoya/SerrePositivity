module
public import SerrePositivity.KST.SConstruction.PrescribedFamilyTransport

/-! # 元の実区間を保持する全パラメータのホモトピー有限列
概要：境界の定数性を要求せず、元の補正の全実区間を保持する有限列を定義する。
方針：始点と終点を型の添字に保ち、各区間の射の列を trace として取り出す。
規約：境界で変化する指定区間を含め、元の区間を代表の類に置き換えない。
使われ方：指定 BF 境界の補正列・射影 trace を保持する厳密化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の実ホモトピーを各区間として保持する有限列。 -/
inductive FamilyHomotopyChain {U E : SSet.{u}} : (U ⟶ E) → (U ⟶ E) → Type u
  | nil (f : U ⟶ E) : FamilyHomotopyChain f f
  | cons {f g h : U ⟶ E} (H : SSet.Homotopy f g) (tail : FamilyHomotopyChain g h) :
      FamilyHomotopyChain f h

/-- 元の有限列に含まれる全区間の実際の円柱の列。 -/
def familyHomotopyChainTrace {U E : SSet.{u}} {f g : U ⟶ E} (c : FamilyHomotopyChain f g) :
    List (U ⊗ (Δ[1] : SSet.{u}) ⟶ E) :=
  match c with
  | .nil _ => []
  | .cons H tail => H.h :: familyHomotopyChainTrace tail

/-- 実区間が空の補正列の両端は厳密に等しい。 -/
lemma familyHomotopyChain_eq_of_trace_nil {U E : SSet.{u}} {f g : U ⟶ E}
    (c : FamilyHomotopyChain f g) (h : familyHomotopyChainTrace c = []) : f = g := by
  cases c with
  | nil => rfl
  | cons H tail => cases h

/-- 同じ始点の表示だけを移し、元の全区間を保持する。 -/
def familyHomotopyChainSourceTransport {U E : SSet.{u}} {f g h : U ⟶ E}
    (c : FamilyHomotopyChain g h) (e : f = g) : FamilyHomotopyChain f h := by
  cases e
  exact c

/-- 始点の表示を移しても、元の全区間の trace は変わらない。 -/
lemma familyHomotopyChainSourceTransport_trace {U E : SSet.{u}} {f g h : U ⟶ E}
    (c : FamilyHomotopyChain g h) (e : f = g) :
    familyHomotopyChainTrace (familyHomotopyChainSourceTransport c e) =
      familyHomotopyChainTrace c := by
  cases e
  rfl

/-- 同じ終点の表示だけを移し、元の全区間を保持する。 -/
def familyHomotopyChainTargetTransport {U E : SSet.{u}} {f g h : U ⟶ E}
    (c : FamilyHomotopyChain f g) (e : g = h) : FamilyHomotopyChain f h := by
  cases e
  exact c

/-- 終点の表示を移しても、元の全区間の trace は変わらない。 -/
lemma familyHomotopyChainTargetTransport_trace {U E : SSet.{u}} {f g h : U ⟶ E}
    (c : FamilyHomotopyChain f g) (e : g = h) :
    familyHomotopyChainTrace (familyHomotopyChainTargetTransport c e) =
      familyHomotopyChainTrace c := by
  cases e
  rfl

/-- 元の全区間を保持した有限列の連結。 -/
def familyHomotopyChainAppend {U E : SSet.{u}} {f g h : U ⟶ E}
    (c : FamilyHomotopyChain f g) (d : FamilyHomotopyChain g h) : FamilyHomotopyChain f h := by
  induction c with
  | nil => exact d
  | cons H tail ih => exact .cons H (ih d)

/-- 有限列の後合成は、元の全区間をそれぞれ後合成する。 -/
def familyHomotopyChainMap {U E B : SSet.{u}} {f g : U ⟶ E}
    (c : FamilyHomotopyChain f g) (p : E ⟶ B) : FamilyHomotopyChain (f ≫ p) (g ≫ p) := by
  induction c with
  | nil => exact .nil _
  | cons H tail ih => exact .cons (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H p) ih

/-- 後合成した有限列の trace は、元の全区間の射影そのもの。 -/
lemma familyHomotopyChainMap_trace {U E B : SSet.{u}} {f g : U ⟶ E}
    (c : FamilyHomotopyChain f g) (p : E ⟶ B) :
    familyHomotopyChainTrace (familyHomotopyChainMap c p) =
      (familyHomotopyChainTrace c).map (· ≫ p) := by
  induction c with
  | nil => rfl
  | cons H tail ih =>
      change (H.h ≫ p) :: familyHomotopyChainTrace (familyHomotopyChainMap tail p) =
        (H.h ≫ p) :: (familyHomotopyChainTrace tail).map (· ≫ p)
      rw [ih]

/-- パラメータの制限も、元の全区間と始点・終点を保持する。 -/
def familyHomotopyChainPrecomp {T U E : SSet.{u}} (j : T ⟶ U) {f g : U ⟶ E}
    (c : FamilyHomotopyChain f g) : FamilyHomotopyChain (j ≫ f) (j ≫ g) := by
  induction c with
  | nil => exact .nil _
  | cons H tail ih => exact .cons (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H j) ih

/-- 制限した有限列の trace は、元の各区間の制限そのもの。 -/
lemma familyHomotopyChainPrecomp_trace {T U E : SSet.{u}} (j : T ⟶ U) {f g : U ⟶ E}
    (c : FamilyHomotopyChain f g) :
    familyHomotopyChainTrace (familyHomotopyChainPrecomp j c) =
      (familyHomotopyChainTrace c).map ((j ▷ (Δ[1] : SSet.{u})) ≫ ·) := by
  induction c with
  | nil => rfl
  | cons H tail ih =>
      change ((j ▷ (Δ[1] : SSet.{u})) ≫ H.h) ::
        familyHomotopyChainTrace (familyHomotopyChainPrecomp j tail) =
        ((j ▷ (Δ[1] : SSet.{u})) ≫ H.h) ::
          (familyHomotopyChainTrace tail).map ((j ▷ (Δ[1] : SSet.{u})) ≫ ·)
      rw [ih]

/-- 元の実円柱一つからなる補正有限列。 -/
def familyHomotopyChainSingle {U E : SSet.{u}} {f g : U ⟶ E} (H : SSet.Homotopy f g) :
    FamilyHomotopyChain f g := .cons H (.nil g)

/-- 一区間の補正の trace は、元の同じ実円柱だけを含む。 -/
lemma familyHomotopyChainSingle_trace {U E : SSet.{u}} {f g : U ⟶ E} (H : SSet.Homotopy f g) :
    familyHomotopyChainTrace (familyHomotopyChainSingle H) = [H.h] := rfl

/-- 連結した補正の trace は、元の全区間の順序を保った連結そのもの。 -/
lemma familyHomotopyChainAppend_trace {U E : SSet.{u}} {f g h : U ⟶ E}
    (c : FamilyHomotopyChain f g) (d : FamilyHomotopyChain g h) :
    familyHomotopyChainTrace (familyHomotopyChainAppend c d) =
      familyHomotopyChainTrace c ++ familyHomotopyChainTrace d := by
  induction c with
  | nil => rfl
  | cons H tail ih =>
      change H.h :: familyHomotopyChainTrace (familyHomotopyChainAppend tail d) =
        H.h :: (familyHomotopyChainTrace tail ++ familyHomotopyChainTrace d)
      rw [ih]

end SerrePositivity.KST.SConstruction
