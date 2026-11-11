module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalMappingSpace
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：終対象の頂点が張る全部分複体。
方針：全ての頂点が条件を満たす単体を取り、境界の充填を周囲から制限する。
規約：非空の場合に可縮性を主張する。
使われ方：HTT Proposition 1.2.12.9、Kerodon §4.7.3（Tag 02H6）。

対応節は Kerodon 4.7（Tag 05EA）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories

/-- 概要：指定した頂点の集合が張る全部分複体。
方針：零単体からの全ての引き戻しが P を満たす単体を取る。
規約：P の同型不変性などを仮定しない。
使われ方：HTT Proposition 1.2.12.9 の終対象の部分複体。 -/
@[kerodon 01CW]
def fullSubcomplexOnVertices (X : SSet.{u}) (P : X _⦋0⦌ → Prop) : X.Subcomplex where
  obj n := {s | ∀ v : ⦋0⦌ ⟶ n.unop, P (X.map v.op s)}
  map {n m} α s hs v := by
    have h := hs (v ≫ α.unop)
    simpa only [op_comp, Quiver.Hom.op_unop, CategoryTheory.Functor.map_comp_apply] using h

/-- 概要：全部分複体の零単体は指定された頂点条件を満たす。
方針：恒等写像による引き戻しを取る。
規約：部分型の値を元の頂点として読む。
使われ方：HTT Proposition 1.2.12.9 の終対象の頂点。 -/
lemma fullSubcomplexOnVertices_vertex {X : SSet.{u}} {P : X _⦋0⦌ → Prop}
    (x : (fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌) : P x.val := by
  simpa only [op_id, CategoryTheory.Functor.map_id_apply] using x.property (𝟙 ⦋0⦌)

/-- 概要：標準単体からの射の全頂点が P に属すれば全部分複体へ持ち上がる。
方針：各単体の頂点を Yoneda の自然性で元の標準単体の頂点に直す。
規約：全ての零単体からの射で条件を確認する。
使われ方：HTT Proposition 1.2.12.9 の境界充填の制限。 -/
def fullSubcomplexLiftSimplex {X : SSet.{u}} (P : X _⦋0⦌ → Prop) {n : ℕ}
    (F : (Δ[n] : SSet.{u}) ⟶ X)
    (hF : ∀ v : ⦋0⦌ ⟶ ⦋n⦌, P (SSet.yonedaEquiv (stdSimplex.map v ≫ F))) :
    (Δ[n] : SSet.{u}) ⟶ (fullSubcomplexOnVertices X P : SSet.{u}) where
  app d := ↾fun s ↦ ⟨F.app d s, by
    intro v
    have he : X.map v.op (F.app d s) = F.app (Opposite.op ⦋0⦌) ((Δ[n]).map v.op s) :=
      (ConcreteCategory.congr_hom (F.naturality v.op) s).symm
    rw [he]
    exact hF (v ≫ s.down)⟩
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (F.naturality α) s

/-- 概要：終対象の頂点が張る全部分複体。
方針：頂点の条件を終対象の充填条件とする。
規約：空の場合も単体集合として定義する。
使われ方：HTT Proposition 1.2.12.9、Kerodon §4.7.3（Tag 02H6）。 -/
@[kerodon 02HM]
def terminalVertices (X : SSet.{u}) : X.Subcomplex :=
  fullSubcomplexOnVertices X _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex

/-- 概要：全部分複体への標準単体の持ち上げを含めると元の射。
方針：部分型の値を取る。
規約：頂点の条件の証明には依存しない。
使われ方：HTT Proposition 1.2.12.9 の境界制限。 -/
lemma fullSubcomplexLiftSimplex_ι {X : SSet.{u}} (P : X _⦋0⦌ → Prop) {n : ℕ}
    (F : (Δ[n] : SSet.{u}) ⟶ X)
    (hF : ∀ v : ⦋0⦌ ⟶ ⦋n⦌, P (SSet.yonedaEquiv (stdSimplex.map v ≫ F))) :
    fullSubcomplexLiftSimplex P F hF ≫ (fullSubcomplexOnVertices X P).ι = F := rfl

/-- 概要：終対象の全部分複体は、終対象が存在すれば可縮な Kan 複体。
方針：正次元の境界の最後の頂点を終対象として充填し、全頂点が元の境界に属すことを使う。
規約：元の単体集合に quasicategory 性は仮定しない。
使われ方：HTT Proposition 1.2.12.9、Kerodon §4.7.3（Tag 02H6）。 -/
@[kerodon 02HM]
lemma terminalVertices_isContractibleKan {X : SSet.{u}}
    (hne : ∃ x : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (terminalVertices X : SSet.{u}) := by
  intro n b
  cases n with
  | zero =>
    obtain ⟨x, hx⟩ := hne
    let t : (terminalVertices X : SSet.{u}) _⦋0⦌ := ⟨x, by
      intro v
      have hv : v = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
      simpa only [hv, op_id, CategoryTheory.Functor.map_id_apply] using hx⟩
    exact ⟨SSet.const t, boundary.hom_ext₀⟩
  | succ n =>
    let b' := b ≫ (terminalVertices X).ι
    let x := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b')
    have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x := by
      exact fullSubcomplexOnVertices_vertex
        (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b))
    obtain ⟨F, hF⟩ := hx n b' (SSet.yonedaEquiv.symm_apply_apply _).symm
    have hv (v : ⦋0⦌ ⟶ ⦋n + 1⦌) :
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (SSet.yonedaEquiv (stdSimplex.map v ≫ F)) := by
      have he : stdSimplex.map v =
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (v.toOrderHom 0) ≫ (boundary (n + 1)).ι := by
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex_ι]
        apply SSet.yonedaEquiv.injective
        rw [Equiv.apply_symm_apply]
        apply stdSimplex.ext
        intro i
        fin_cases i
        rfl
      rw [he, Category.assoc, hF]
      exact fullSubcomplexOnVertices_vertex
        (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (v.toOrderHom 0) ≫ b))
    refine ⟨fullSubcomplexLiftSimplex _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex F hv, ?_⟩
    apply (cancel_mono (terminalVertices X).ι).1
    change (boundary (n + 1)).ι ≫ fullSubcomplexLiftSimplex _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex F hv ≫
      (fullSubcomplexOnVertices X _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex).ι = b'
    rw [fullSubcomplexLiftSimplex_ι]
    exact hF

/-- 概要：全頂点が条件を満たす射を全部分複体へ持ち上げる。
方針：各単体の頂点の像を零次成分の条件と自然性で確認する。
規約：任意の始域を扱う。
使われ方：Kerodon §4.4.3（Tag 01CZ）、§4.5.3（Tag 032Y） の関手の同値の path の部分複体。 -/
def fullSubcomplexLift {A X : SSet.{u}} (P : X _⦋0⦌ → Prop) (f : A ⟶ X)
    (hf : ∀ a : A _⦋0⦌, P (f.app (Opposite.op ⦋0⦌) a)) :
    A ⟶ (fullSubcomplexOnVertices X P : SSet.{u}) where
  app d := ↾fun a ↦ ⟨f.app d a, by
    intro v
    have he := ConcreteCategory.congr_hom (f.naturality v.op) a
    exact he ▸ hf (A.map v.op a)⟩
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (f.naturality α) a

/-- 概要：全部分複体への持ち上げを含めると元の射。
方針：部分型の値を取る。
規約：頂点条件の証明には依存しない。
使われ方：Kerodon §4.4.3（Tag 01CZ）、§4.5.3（Tag 032Y） の path の比較。 -/
lemma fullSubcomplexLift_ι {A X : SSet.{u}} (P : X _⦋0⦌ → Prop) (f : A ⟶ X)
    (hf : ∀ a : A _⦋0⦌, P (f.app (Opposite.op ⦋0⦌) a)) :
    fullSubcomplexLift P f hf ≫ (fullSubcomplexOnVertices X P).ι = f := rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
