module
public import SerrePositivity.KST.SConstruction.FirstRowCofiberData

/-! # 全部分複体の始対象・終対象
概要：周囲で始対象・終対象である全部分複体の頂点は、全部分複体でも同じ性質を持つ。
方針：正次元の境界が全頂点を含むことから周囲の充填を持ち上げる。
規約：quasicategory 性は不要。使われ方：HTT §1.2.12、S• の零対象。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：全部分複体の包含は全頂点を含む単射に対して持ち上げ性を持つ。
方針：頂点条件を指定部分から回収し、与えられた全体の射を部分複体に持ち上げる。
規約：単射性は不要で、頂点での全射性のみを使う。
使われ方：正次元の境界の充填を全部分複体へ戻す。 -/
lemma fullSubcomplex_hasLiftingProperty_of_vertexSurjective {A B X : SSet.{u}}
    (P : X _⦋0⦌ → Prop) (i : A ⟶ B)
    (hi : Function.Surjective (i.app (Opposite.op ⦋0⦌))) :
    HasLiftingProperty i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι := by
  constructor
  intro a b sq
  have hv (v : B _⦋0⦌) : P (b.app (Opposite.op ⦋0⦌) v) := by
    obtain ⟨u, rfl⟩ := hi v
    have he := ConcreteCategory.congr_hom (NatTrans.congr_app sq.w (Opposite.op ⦋0⦌)) u
    change (a.app (Opposite.op ⦋0⦌) u).val = b.app (Opposite.op ⦋0⦌)
      (i.app (Opposite.op ⦋0⦌) u) at he
    rw [← he]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) u)
  refine CommSq.HasLift.mk' {
    l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P b hv
    fac_left := ?_
    fac_right := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι P b hv }
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι).1
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
  exact sq.w.symm

/-- 概要：周囲で始対象である全部分複体の頂点は全部分複体でも始対象。
方針：周囲で境界を充填し、全頂点を含む境界での持ち上げを使う。
規約：P は任意。使われ方：S_n の零図式の始対象性。 -/
lemma isInitialVertex_fullSubcomplex_of_ambient {X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌) (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v := by
  intro n b hb
  let j := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ (b ≫ j) = SSet.yonedaEquiv.symm v.val := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
    rfl
  obtain ⟨F, hF⟩ := hv n (b ≫ j) he
  have := fullSubcomplex_hasLiftingProperty_of_vertexSurjective P
    (boundary (n + 1)).ι (boundary_vertex_surjective n)
  have sq : CommSq b (boundary (n + 1)).ι j F := ⟨hF.symm⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 概要：周囲で終対象である全部分複体の頂点は全部分複体でも終対象。
方針：周囲で境界を充填し、全部分複体の包含で持ち上げる。
規約：P は任意。使われ方：S_n の零図式の終対象性。 -/
lemma isTerminalVertex_fullSubcomplex_of_ambient {X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌) (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex v.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex v := by
  intro n b hb
  let j := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ (b ≫ j) = SSet.yonedaEquiv.symm v.val := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
    rfl
  obtain ⟨F, hF⟩ := hv n (b ≫ j) he
  have := fullSubcomplex_hasLiftingProperty_of_vertexSurjective P
    (boundary (n + 1)).ι (boundary_vertex_surjective n)
  have sq : CommSq b (boundary (n + 1)).ι j F := ⟨hF.symm⟩
  exact ⟨sq.lift, sq.fac_left⟩

end SerrePositivity.KST.SConstruction
