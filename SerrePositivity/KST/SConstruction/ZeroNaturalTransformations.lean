module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroBoundaryExtension
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialPrismBoundary
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalPrismBoundary
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Pointed
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary

/-! # 零対象上で恒等な零射の自然変換
概要：零対象から恒等関手へ、恒等関手から零対象への自然変換を零対象上で厳密に固定して選ぶ。
方針：prism の両端と指定した部分を貼り、新しい単体の始点または終点の普遍性で延長する。
規約：自然変換を同値とは主張しない。使われ方：Fiore–Pieper Lemma 4.24、Example 9.14 の零射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：零対象で一定な部分を固定して、任意の図式と零対象の間の prism を延長できる。
方針：両端と指定部分の和を貼り、新しい単体の始点または終点が零対象であることを使う。
規約：false は零対象から図式へ、true は図式から零対象へ。使われ方：零射の相対的な自然変換。 -/
lemma exists_relative_zeroPrism {B C : SSet.{u}} (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (b : Bool)
    (S : B.Subcomplex) (f : B ⟶ C) (hf : S.ι ≫ f = SSet.const z.vertex) :
    ∃ H : (Δ[1] : SSet.{u}) ⊗ B ⟶ C,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ H = (if b then f else SSet.const z.vertex) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ H = (if b then SSet.const z.vertex else f) ∧
      (Δ[1] ◁ S.ι) ≫ H = SSet.const z.vertex := by
  let f₀ : B ⟶ C := if b then f else SSet.const z.vertex
  let f₁ : B ⟶ C := if b then SSet.const z.vertex else f
  let T := boundary.{u} 1
  let q := Subcomplex.unionProd.isPushout T S
  let h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f₀ f₁
  have hf₀ : S.ι ≫ f₀ = SSet.const z.vertex := by
    cases b <;> simp only [f₀, Bool.false_eq_true, ↓reduceIte, SSet.comp_const, hf]
  have hf₁ : S.ι ≫ f₁ = SSet.const z.vertex := by
    cases b <;> simp only [f₁, Bool.false_eq_true, ↓reduceIte, SSet.comp_const, hf]
  have hw : (T.ι ▷ (S : SSet.{u})) ≫ (SSet.const z.vertex : Δ[1] ⊗ (S : SSet.{u}) ⟶ C) =
      ((T : SSet.{u}) ◁ S.ι) ≫ h := by
    rw [SSet.comp_const, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_naturality, hf₀, hf₁]
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro v
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z.vertex n =
      if v.1.val 0 = 0 then _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z.vertex n else _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z.vertex n
    split_ifs <;> rfl
  let a := q.desc (SSet.const z.vertex) h hw
  have ha₁ : Subcomplex.unionProd.ι₁ T S ≫ a = SSet.const z.vertex := q.inl_desc _ _ _
  have ha₂ : Subcomplex.unionProd.ι₂ T S ≫ a = h := q.inr_desc _ _ _
  let A := Subcomplex.unionProd T S
  have hvT (x : (Δ[1] : SSet.{u}) _⦋0⦌) : x ∈ T.obj (Opposite.op ⦋0⦌) := by
    have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary 0 (stdSimplex.obj₀Equiv x)
    rw [Equiv.symm_apply_apply] at hx
    exact hx
  have hA : ∀ v : ((Δ[1] : SSet.{u}) ⊗ B) _⦋0⦌, v ∈ A.obj (Opposite.op ⦋0⦌) := by
    intro v
    exact (Subcomplex.mem_unionProd_iff T S v).2
      (Or.inr (hvT v.1))
  have eval_a (v : ((Δ[1] : SSet.{u}) ⊗ B) _⦋0⦌) :
      a.app (Opposite.op ⦋0⦌) ⟨v, hA v⟩ =
        h.app (Opposite.op ⦋0⦌)
          (⟨v.1, hvT v.1⟩, v.2) := by
    let w : ((T : SSet.{u}) ⊗ B) _⦋0⦌ := (⟨v.1, hvT v.1⟩, v.2)
    exact ConcreteCategory.congr_hom (NatTrans.congr_app ha₂ (Opposite.op ⦋0⦌)) w
  obtain ⟨H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_extension_of_initial_or_terminal_endpoints A hA a (by
    intro n s hs
    have hi (i : Fin 2) : s.1 ∉ (horn 1 i).obj (Opposite.op ⦋n + 1⦌) := by
      intro hi
      obtain ⟨k, _hk, hr⟩ := (mem_horn_iff_notMem_range s.1 i).1 hi
      exact hs ((Subcomplex.mem_unionProd_iff T S s).2
        (Or.inr ((mem_boundary_iff_notMem_range s.1).2 ⟨k, hr⟩)))
    cases b with
    | false =>
      left
      rw [eval_a]
      have ht := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_interval_firstVertex_of_notMem_lastHorn s.1 (hi 1)
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (if (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s.1 : (Δ[1] : SSet.{u}) _⦋0⦌) 0 = 0
        then _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z.vertex 0 else f.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s.2))
      rw [ht, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
      exact z.isInitial
    | true =>
      right
      rw [eval_a]
      have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stable_interval_lastVertex_of_notMem_firstHorn s.1 (hi 0)
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (if (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s.1 : (Δ[1] : SSet.{u}) _⦋0⦌) 0 = 0
        then f.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s.2) else _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z.vertex 0)
      rw [ht, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
      exact z.isTerminal)
  have hb : (T.ι ▷ B) ≫ H = h := by
    rw [← Subcomplex.unionProd.ι₂_ι T S, Category.assoc, hH, ha₂]
  refine ⟨H, ?_, ?_, ?_⟩
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι 0 B, Category.assoc, hb, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_zero]
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι 1 B, Category.assoc, hb, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_one]
  · rw [← Subcomplex.unionProd.ι₁_ι T S, Category.assoc, hH, ha₁]

/-- 概要：零対象から恒等関手へ、または恒等関手から零対象への自然変換を選ぶ。
方針：零対象の生成部分複体を固定する相対 prism の延長から選ぶ。
規約：false は零対象から、true は零対象へ。使われ方：McCarthy ホモトピーの零射。 -/
def zeroNaturalTransformation {C : SSet.{u}} (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (b : Bool) :
    (Δ[1] : SSet.{u}) ⊗ C ⟶ C :=
  Classical.choose (exists_relative_zeroPrism z b (Subcomplex.ofSimplex z.vertex) (𝟙 C)
    (by rw [Category.comp_id, Subcomplex.ofSimplex_ι]))

/-- 概要：選んだ零射の自然変換の始点は指定した関手。
方針：相対 prism の始点の仕様。
規約：射の厳密な等号。使われ方：McCarthy の端点の照合。 -/
lemma zeroNaturalTransformation_zero {C : SSet.{u}} (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (b : Bool) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 C ≫ zeroNaturalTransformation z b =
      (if b then 𝟙 C else SSet.const z.vertex) :=
  (Classical.choose_spec (exists_relative_zeroPrism z b (Subcomplex.ofSimplex z.vertex) (𝟙 C)
    (by rw [Category.comp_id, Subcomplex.ofSimplex_ι]))).1

/-- 概要：選んだ零射の自然変換の終点は指定した関手。
方針：相対 prism の終点の仕様。
規約：射の厳密な等号。使われ方：McCarthy の端点の照合。 -/
lemma zeroNaturalTransformation_one {C : SSet.{u}} (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (b : Bool) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 C ≫ zeroNaturalTransformation z b =
      (if b then SSet.const z.vertex else 𝟙 C) :=
  (Classical.choose_spec (exists_relative_zeroPrism z b (Subcomplex.ofSimplex z.vertex) (𝟙 C)
    (by rw [Category.comp_id, Subcomplex.ofSimplex_ι]))).2.1

/-- 概要：選んだ零射の自然変換は零対象上で恒等となる一定の prism。
方針：相対延長で零対象の生成部分複体を厳密に固定した仕様。
規約：全ての高次単体で固定する。使われ方：McCarthy の零対角の正規化。 -/
lemma zeroNaturalTransformation_fixed {C : SSet.{u}} (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (b : Bool) :
    (Δ[1] ◁ (Subcomplex.ofSimplex z.vertex).ι) ≫ zeroNaturalTransformation z b =
      SSet.const z.vertex :=
  (Classical.choose_spec (exists_relative_zeroPrism z b (Subcomplex.ofSimplex z.vertex) (𝟙 C)
    (by rw [Category.comp_id, Subcomplex.ofSimplex_ι]))).2.2

/-- 概要：零対象で一定な任意の図式に対し、選んだ零射の自然変換は一定。
方針：一定図式を零対象の生成部分複体へ持ち上げ、相対固定の式を適用する。
規約：任意のパラメーターの全単体での等号。使われ方：McCarthy の零対角の固定。 -/
lemma zeroNaturalTransformation_constant {A C : SSet.{u}} (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (b : Bool) :
    (Δ[1] ◁ (SSet.const z.vertex : A ⟶ C)) ≫ zeroNaturalTransformation z b =
      SSet.const z.vertex := by
  let g : A ⟶ (Subcomplex.ofSimplex z.vertex : SSet.{u}) :=
    SSet.const ⟨z.vertex, Subcomplex.mem_ofSimplex_obj z.vertex⟩
  have hg : g ≫ (Subcomplex.ofSimplex z.vertex).ι = SSet.const z.vertex := by
    dsimp only [g]
    rw [SSet.const_comp]
    rfl
  rw [← hg, whiskerLeft_comp, Category.assoc, zeroNaturalTransformation_fixed, SSet.comp_const]

end SerrePositivity.KST.SConstruction
