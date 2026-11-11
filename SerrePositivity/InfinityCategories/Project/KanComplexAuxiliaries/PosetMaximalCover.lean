module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.Order.Max

/-!
概要：極大点を一つ追加する順序集合の nerve を、全部分複体の pushout として捉える。
方針：単体の最後の頂点で被覆を証明し、合併・共通部分の合併と共通部分の正方形を作る。
規約：有限性を要求せず、全次数と元の包含を保持する。
使われ方：有限半順序形状の Ind 表示で、一般の試験族を保って点を追加する。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
set_option backward.isDefEq.respectTransparency false
/-- 概要：極大点の除去部分と下方部分は全 nerve を覆う。
方針：各鎖の最後の頂点を調べる。規約：全次数。使われ方：点追加の貼り合わせ。 -/
lemma posetNerve_maximal_cover {P : Type u} [PartialOrder P] (a : P) (ha : IsMax a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ nerveEquiv v ≠ a) ⊔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ nerveEquiv v ≤ a) = ⊤ := by
  classical
  apply le_antisymm le_top
  intro n s hs
  change (∀ v : ⦋0⦌ ⟶ n.unop, nerveEquiv ((nerve P).map v.op s) ≠ a) ∨
    (∀ v : ⦋0⦌ ⟶ n.unop, nerveEquiv ((nerve P).map v.op s) ≤ a)
  by_cases h : s.obj (Fin.last n.unop.len) = a
  · right
    intro v
    change s.obj (v.toOrderHom 0) ≤ a
    rw [← h]
    exact s.monotone (Fin.le_last _)
  · left
    intro v hv
    change s.obj (v.toOrderHom 0) = a at hv
    have hle : a ≤ s.obj (Fin.last n.unop.len) := by
      rw [← hv]
      exact s.monotone (Fin.le_last _)
    exact h (le_antisymm (ha hle) hle)
/-- 概要：点除去部分と下方部分の共通部分は厳密下方部分。
方針：全頂点の不等式。規約：極大性は不要。使われ方：点追加の共通境界。 -/
lemma posetNerve_maximal_intersection {P : Type u} [PartialOrder P] (a : P) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ nerveEquiv v ≠ a) ⊓
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ nerveEquiv v ≤ a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ nerveEquiv v < a) := by
  ext n s
  change ((∀ v : ⦋0⦌ ⟶ n.unop, nerveEquiv ((nerve P).map v.op s) ≠ a) ∧
    (∀ v : ⦋0⦌ ⟶ n.unop, nerveEquiv ((nerve P).map v.op s) ≤ a)) ↔
    ∀ v : ⦋0⦌ ⟶ n.unop, nerveEquiv ((nerve P).map v.op s) < a
  exact ⟨fun h v ↦ lt_of_le_of_ne (h.2 v) (h.1 v),
    fun h ↦ ⟨fun v ↦ (h v).ne, fun v ↦ (h v).le⟩⟩

/-- 概要：元の点除去部分と下方部分の包含は実 pushout を与える合併と共通部分の正方形。
方針：合併と共通部分を照合。規約：元の部分複体。使われ方：`isPushout` による貼合せ。 -/
lemma posetNerve_maximal_bicartSq {P : Type u} [PartialOrder P] (a : P) (ha : IsMax a) :
    SSet.Subcomplex.BicartSq
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ nerveEquiv v < a))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ nerveEquiv v ≠ a))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ nerveEquiv v ≤ a)) ⊤ :=
  ⟨posetNerve_maximal_cover a ha, posetNerve_maximal_intersection a⟩

/-- 概要：元の nerve 自体を頂点とする包含の正方形は pushout。
方針：全部分複体の標準同型を使用。規約：包含を保持。使われ方：点追加の境界。 -/
lemma posetNerve_maximal_isPushout {P : Type u} [PartialOrder P]
    (a : P) (ha : IsMax a) :
    let sq := posetNerve_maximal_bicartSq a ha
    IsPushout (Subcomplex.homOfLE sq.le₁₂) (Subcomplex.homOfLE sq.le₁₃)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ nerveEquiv v ≠ a)).ι
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ nerveEquiv v ≤ a)).ι := by
  apply (posetNerve_maximal_bicartSq a ha).isPushout.of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Subcomplex.topIso (nerve P))
  all_goals simp [Subcomplex.topIso_hom]

/-- 概要：任意の試験族との積も、元の包含による実 pushout。
方針：積の余極限保存。規約：試験族の有限性は不要。使われ方：相対補間の境界。 -/
lemma posetNerve_maximal_product_isPushout {P : Type u} [PartialOrder P]
    (a : P) (ha : IsMax a) (B : SSet.{u}) :
    let sq := posetNerve_maximal_bicartSq a ha
    IsPushout (Subcomplex.homOfLE sq.le₁₂ ▷ B) (Subcomplex.homOfLE sq.le₁₃ ▷ B)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ nerveEquiv v ≠ a)).ι ▷ B)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ nerveEquiv v ≤ a)).ι ▷ B) := by
  exact (posetNerve_maximal_isPushout a ha).map (tensorRight B)

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
