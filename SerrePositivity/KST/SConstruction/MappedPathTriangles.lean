module
public import SerrePositivity.KST.SConstruction.ContractiblePathComparison

/-! # 中央が恒等辺へ写る指定道の三角形
概要：可縮なパラメーターの三辺列から、評価後の指定二辺と対角辺の実三角形を得る。
方針：パラメーター内を二つの三角形に分け、恒等辺を消して再び二単体へ戻す。
規約：辺の underlying 一単体の等号を使い、端点の付け直しで辺を変えない。
使われ方：円筒横断を消し、選択済みの自然性の辺を二つの因子辺へ分解する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 一単体が同じ辺は始点も等しい。 -/
lemma edge_source_eq_of_edge_eq {K : SSet.{u}} {x₀ x₁ y₀ y₁ : K _⦋0⦌}
    (e : K.Edge x₀ x₁) (f : K.Edge y₀ y₁) (h : e.edge = f.edge) : x₀ = y₀ :=
  e.src_eq.symm.trans ((congrArg (K.δ 1) h).trans f.src_eq)

/-- 一単体が同じ辺は終点も等しい。 -/
lemma edge_target_eq_of_edge_eq {K : SSet.{u}} {x₀ x₁ y₀ y₁ : K _⦋0⦌}
    (e : K.Edge x₀ x₁) (f : K.Edge y₀ y₁) (h : e.edge = f.edge) : x₁ = y₁ :=
  e.tgt_eq.symm.trans ((congrArg (K.δ 0) h).trans f.tgt_eq)

/-- 可縮なパラメーターの中央辺が恒等辺へ写れば、指定二辺と対角辺を保つ実三角形がある。 -/
lemma contractibleKan_mapped_three_edge_triangle {P K : SSet.{u}} [Quasicategory K]
    (hP : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan P) (F : P ⟶ K)
    {p₀ p₁ p₂ p₃ : P _⦋0⦌}
    (a : P.Edge p₀ p₁) (b : P.Edge p₁ p₂) (c : P.Edge p₂ p₃) (d : P.Edge p₀ p₃)
    {x₀ x₁ x₂ : K _⦋0⦌} (e : K.Edge x₀ x₁) (f : K.Edge x₁ x₂) (g : K.Edge x₀ x₂)
    (ha : (a.map F).edge = e.edge) (hb : (b.map F).edge = (SSet.Edge.id x₁).edge)
    (hc : (c.map F).edge = f.edge) (hd : (d.map F).edge = g.edge) :
    Nonempty (SSet.Edge.CompStruct e f g) := by
  obtain ⟨v⟩ := (hP.isTerminalVertex p₂).nonempty_edge p₀
  let q := SSet.Edge.ofTruncated v
  let q' : K.Edge x₀ x₁ := (q.map F).ofEq
    (edge_source_eq_of_edge_eq (a.map F) e ha)
    (edge_target_eq_of_edge_eq (b.map F) (.id x₁) hb)
  obtain ⟨t₀₁₂⟩ := contractibleKan_nonempty_compStruct hP a b q
  obtain ⟨t₀₂₃⟩ := contractibleKan_nonempty_compStruct hP q c d
  have h₁ := SSet.HomotopyCategory.homMk_comp_homMk
    ((t₀₁₂.map F).ofEq ha hb (show (q.map F).edge = q'.edge from rfl))
  have h₂ := SSet.HomotopyCategory.homMk_comp_homMk
    ((t₀₂₃.map F).ofEq (show (q.map F).edge = q'.edge from rfl) hc hd)
  have hi := SSet.HomotopyCategory.homMk_id x₁
  rw [hi, Category.comp_id] at h₁
  exact nonemptyCompStruct_of_homMk_fac e f g (by rw [h₁]; exact h₂)


/-- 三角形を写した後、指定対角辺と同じ一単体を保って因子分解三角形を回収する。 -/
lemma exists_mapped_factorization {K L : SSet.{u}} {x₀ x₁ x₂ : K _⦋0⦌}
    (a : K.Edge x₀ x₁) (b : K.Edge x₁ x₂) (e : K.Edge x₀ x₂)
    (h : SSet.Edge.CompStruct a b e) (F : K ⟶ L)
    {y₀ y₂ : L _⦋0⦌} (g : L.Edge y₀ y₂) (he : (e.map F).edge = g.edge) :
    ∃ (y₁ : L _⦋0⦌) (a' : L.Edge y₀ y₁) (b' : L.Edge y₁ y₂),
      a'.edge = (a.map F).edge ∧ b'.edge = (b.map F).edge ∧
        Nonempty (SSet.Edge.CompStruct a' b' g) := by
  let a' := (a.map F).ofEq (edge_source_eq_of_edge_eq (e.map F) g he) rfl
  let b' := (b.map F).ofEq rfl (edge_target_eq_of_edge_eq (e.map F) g he)
  exact ⟨_, a', b', rfl, rfl, ⟨(h.map F).ofEq rfl rfl he⟩⟩

/-- 四つの因子辺の中央の順序交換と両側の三角形を、指定した外側の三角形へ貼る。 -/
lemma nonemptyCompStruct_paste_factorizations {K : SSet.{u}} [Quasicategory K]
    {x₀ x₁ x₂ m₀₁ m₁₂ m₀₂ : K _⦋0⦌}
    (a₀₁ : K.Edge x₀ m₀₁) (b₀₁ : K.Edge m₀₁ x₁) (e₀₁ : K.Edge x₀ x₁)
    (a₁₂ : K.Edge x₁ m₁₂) (b₁₂ : K.Edge m₁₂ x₂) (e₁₂ : K.Edge x₁ x₂)
    (a₀₂ : K.Edge x₀ m₀₂) (b₀₂ : K.Edge m₀₂ x₂) (e₀₂ : K.Edge x₀ x₂)
    (a' : K.Edge m₀₁ m₀₂) (b' : K.Edge m₀₂ m₁₂)
    (h₀₁ : SSet.Edge.CompStruct a₀₁ b₀₁ e₀₁)
    (h₁₂ : SSet.Edge.CompStruct a₁₂ b₁₂ e₁₂)
    (h₀₂ : SSet.Edge.CompStruct a₀₂ b₀₂ e₀₂)
    (hleft : SSet.Edge.CompStruct a₀₁ a' a₀₂)
    (hright : SSet.Edge.CompStruct b' b₁₂ b₀₂)
    (hsquare : SSet.HomotopyCategory.homMk b₀₁ ≫ SSet.HomotopyCategory.homMk a₁₂ =
      SSet.HomotopyCategory.homMk a' ≫ SSet.HomotopyCategory.homMk b') :
    Nonempty (SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) := by
  apply nonemptyCompStruct_of_homMk_fac
  rw [← SSet.HomotopyCategory.homMk_comp_homMk h₀₁,
    ← SSet.HomotopyCategory.homMk_comp_homMk h₁₂]
  calc
    _ = SSet.HomotopyCategory.homMk a₀₁ ≫
        (SSet.HomotopyCategory.homMk b₀₁ ≫ SSet.HomotopyCategory.homMk a₁₂) ≫
        SSet.HomotopyCategory.homMk b₁₂ := by simp only [Category.assoc]
    _ = SSet.HomotopyCategory.homMk a₀₁ ≫
        (SSet.HomotopyCategory.homMk a' ≫ SSet.HomotopyCategory.homMk b') ≫
        SSet.HomotopyCategory.homMk b₁₂ := by rw [hsquare]
    _ = (SSet.HomotopyCategory.homMk a₀₁ ≫ SSet.HomotopyCategory.homMk a') ≫
        (SSet.HomotopyCategory.homMk b' ≫ SSet.HomotopyCategory.homMk b₁₂) := by
      simp only [Category.assoc]
    _ = SSet.HomotopyCategory.homMk e₀₂ := by
      rw [SSet.HomotopyCategory.homMk_comp_homMk hleft,
        SSet.HomotopyCategory.homMk_comp_homMk hright,
        SSet.HomotopyCategory.homMk_comp_homMk h₀₂]

end SerrePositivity.KST.SConstruction
