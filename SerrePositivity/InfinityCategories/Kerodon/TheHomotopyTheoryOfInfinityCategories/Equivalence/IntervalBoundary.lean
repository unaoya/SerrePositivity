module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathReplacement

/-!
概要：区間の境界と二つの端点の図式。
方針：境界の各単体はどちらかの頂点に定値であることを使う。
規約：時刻零と時刻一の順に指定する。
使われ方：HTT §2.1.2、Kerodon §4.5.3（Tag 032Y） の二端点を固定した充填。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：区間の境界の単体は最初の値に定値。
方針：値域から欠ける頂点を選び、二点鎖の残りの値は一意であることを使う。
規約：任意の次数の任意の頂点を扱う。
使われ方：Kerodon §4.5.3（Tag 032Y） の二端点の図式。 -/
lemma boundaryOne_simplex_constant {n : ℕ} (s : (boundary 1 : SSet.{u}) _⦋n⦌)
    (j : Fin (n + 1)) : s.val j = s.val 0 := by
  obtain ⟨k, hk⟩ := (mem_boundary_iff_notMem_range s.val).1 s.property
  have h₀ : s.val 0 ≠ k := fun h ↦ hk ⟨0, h⟩
  have hj : s.val j ≠ k := fun h ↦ hk ⟨j, h⟩
  apply Fin.ext
  have ha := (s.val 0).isLt
  have hb := (s.val j).isLt
  have hc := k.isLt
  have h₀' : (s.val 0).val ≠ k.val := fun h ↦ h₀ (Fin.ext h)
  have hj' : (s.val j).val ≠ k.val := fun h ↦ hj (Fin.ext h)
  omega

/-- 概要：二つの射から区間の境界上の図式を作る。
方針：境界の単体が時刻零か一かで指定された射を使う。
規約：標準区間を第一因子に置く。
使われ方：Kerodon §4.5.3（Tag 032Y） の端点を同時に指定する射。 -/
def intervalBoundaryDiagram {A Y : SSet.{u}} (f g : A ⟶ Y) :
    (boundary 1 : SSet.{u}) ⊗ A ⟶ Y where
  app n := by
    obtain ⟨⟨d⟩⟩ := n
    exact ↾(fun x ↦ if x.1.val 0 = 0 then f.app _ x.2 else g.app _ x.2)
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    rintro ⟨s, x⟩
    change (if s.val (α.unop.toOrderHom 0) = 0 then
      f.app _ (A.map α x) else g.app _ (A.map α x)) =
      Y.map α (if s.val 0 = 0 then f.app _ x else g.app _ x)
    rw [boundaryOne_simplex_constant s]
    split <;> simp only [CategoryTheory.NatTrans.naturality_apply]

/-- 概要：時刻零の端点は区間の境界に属する。
方針：時刻一を値に取らない。
規約：任意の単体集合をパラメーターに持つ。
使われ方：Kerodon §4.5.3（Tag 032Y） の端点の制限。 -/
noncomputable def intervalBoundaryEndpoint (i : Fin 2) (A : SSet.{u}) :
    A ⟶ (boundary 1 : SSet.{u}) ⊗ A :=
  lift (SSet.const ⟨stdSimplex.obj₀Equiv.symm i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary 0 i⟩) (𝟙 A)

/-- 概要：境界の端点を区間へ含めると prism の端点。
方針：部分型の値を取る。
規約：両方の端点を扱う。
使われ方：Kerodon §4.5.3（Tag 032Y） の端点の識別。 -/
lemma intervalBoundaryEndpoint_ι (i : Fin 2) (A : SSet.{u}) :
    intervalBoundaryEndpoint i A ≫ ((boundary 1).ι ▷ A) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i A := rfl

/-- 概要：二端点の図式を零で制限すると第一の射。
方針：定値の零と恒等射を評価する。
規約：厳密な等式。
使われ方：Kerodon §4.5.3（Tag 032Y） の始点の識別。 -/
lemma intervalBoundaryDiagram_zero {A Y : SSet.{u}} (f g : A ⟶ Y) :
    intervalBoundaryEndpoint 0 A ≫ intervalBoundaryDiagram f g = f := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro x
  change (if (0 : Fin 2) = 0 then f.app _ x else g.app _ x) = _
  simp

/-- 概要：二端点の図式を一で制限すると第二の射。
方針：定値の一と恒等射を評価する。
規約：厳密な等式。
使われ方：Kerodon §4.5.3（Tag 032Y） の終点の識別。 -/
lemma intervalBoundaryDiagram_one {A Y : SSet.{u}} (f g : A ⟶ Y) :
    intervalBoundaryEndpoint 1 A ≫ intervalBoundaryDiagram f g = g := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro x
  change (if (1 : Fin 2) = 0 then f.app _ x else g.app _ x) = _
  simp

/-- 概要：二端点の図式はパラメーターの射との合成に自然。
方針：同じ端点で分岐する定義を各次数で比較する。
規約：パラメーターだけを変える。
使われ方：Kerodon §4.5.3（Tag 032Y） の境界の貼り合わせ。 -/
lemma intervalBoundaryDiagram_naturality {A B Y : SSet.{u}} (i : A ⟶ B) (f g : B ⟶ Y) :
    ((boundary 1 : SSet.{u}) ◁ i) ≫ intervalBoundaryDiagram f g =
      intervalBoundaryDiagram (i ≫ f) (i ≫ g) := rfl

/-- 概要：prism の区間の境界への制限は二端点の図式。
方針：境界の単体の定値性を使って二つの端点に分ける。
規約：任意の prism を扱う。
使われ方：Kerodon §4.5.3（Tag 032Y） の prism の境界条件。 -/
lemma intervalBoundaryDiagram_restrict {A Y : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y) :
    ((boundary 1).ι ▷ A) ≫ H =
      intervalBoundaryDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, x⟩
  change H.app (Opposite.op ⦋d⦌) (s.val, x) =
    (if s.val 0 = 0 then
      H.app (Opposite.op ⦋d⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) d, x)
    else H.app (Opposite.op ⦋d⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 1) d, x))
  split_ifs with hs
  · congr 1
    refine Prod.ext ?_ rfl
    apply stdSimplex.ext
    intro j
    exact (boundaryOne_simplex_constant s j).trans hs
  · have hs' : s.val 0 = 1 := by
      apply Fin.ext
      change (s.val 0).val = 1
      have h := (s.val 0).isLt
      have h' : (s.val 0).val ≠ 0 := fun h ↦ hs (Fin.ext h)
      omega
    congr 1
    refine Prod.ext ?_ rfl
    apply stdSimplex.ext
    intro j
    exact (boundaryOne_simplex_constant s j).trans hs'

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
